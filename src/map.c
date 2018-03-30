// IMPORTANT NOTE(bill): This is highly unsafe as the key is just a `u64` and the entry value is just a `void *`

typedef struct MapFindResult {
	isize hash_index;
	isize entry_prev;
	isize entry_index;
} MapFindResult;

typedef enum HashKeyKind {
	HashKey_Default,
	HashKey_String,
} HashKeyKind;

typedef struct HashKey {
	HashKeyKind kind;
	u64         key;
	String      string;  // if the key is a string
} HashKey;


u64 gb_fnv64a(void const *data, isize len) {
	isize i;
	u64 h = 0xcbf29ce484222325ull;
	u8 const *c = cast(u8 const *)data;

	for (i = 0; i < len; i++) {
		h = (h ^ c[i]) * 0x100000001b3ll;
	}

	return h;
}

u64 hashing_proc(void const *data, isize len) {
	return gb_fnv64a(data, len);
}

HashKey hash_ptr(void *ptr) {
	HashKey h = {HashKey_Default};
	h.key = cast(u64)cast(uintptr)ptr;
	return h;
}
HashKey hash_str(String s) {
	HashKey h = {HashKey_String};
	h.key = hashing_proc(s.text, s.len);
	h.string = s;
	return h;
}
bool hash_key_equal(HashKey a, HashKey b) {
	if (a.key == b.key) {
		// NOTE(bill): If two string's hashes collide, compare the strings themselves
		if (a.kind == HashKey_String) {
			if (b.kind == HashKey_String) {
				return str_eq(a.string, b.string);
			}
			return false;
		}
		return true;
	}
	return false;
}


typedef struct MapEntry {
	HashKey key;
	isize   next;
	void *  value;
} MapEntry;

typedef struct Map {
	isize    *hashes;  // Dynamic buffers
	MapEntry *entries; // Dynamic buffers
} Map;


void  map_init    (Map *m);
void  map_init_cap(Map *m, isize capacity);
void  map_destroy (Map *m);
bool  map_exists  (Map *m, HashKey key);
void *map_get     (Map *m, HashKey key);
void  map_set     (Map *m, HashKey key, void *data);
void  map_remove  (Map *m, HashKey key);
void  map_clear   (Map *m);
void  map_grow    (Map *m);
void  map_rehash  (Map *m, isize new_count);



void map_init(Map *m) {
	map_init_cap(m, 16);
}

void map_init_cap(Map *m, isize capacity) {
	buf_reserve(m->hashes, capacity);
	buf_reserve(m->entries, capacity);
}

void map_destroy(Map *m) {
	buf_free(m->hashes);
	buf_free(m->entries);
	m->hashes = NULL;
	m->entries = NULL;
}


isize map__add_entry(Map *m, HashKey key) {
	MapEntry e = {0};
	e.key = key;
	e.next = -1;
	buf_push(m->entries, e);
	return buf_len(m->entries)-1;
}

MapFindResult map__find(Map *m, HashKey key) {
	MapFindResult fr = {-1, -1, -1};
	if (buf_len(m->hashes) > 0) {
		fr.hash_index = key.key % cast(u64)buf_len(m->hashes);
		fr.entry_index = m->hashes[fr.hash_index];
		while (fr.entry_index >= 0) {
			if (hash_key_equal(m->entries[fr.entry_index].key, key)) {
				return fr;
			}
			fr.entry_prev = fr.entry_index;
			fr.entry_index = m->entries[fr.entry_index].next;
		}
	}
	return fr;
}

MapFindResult map__find_from_entry(Map *m, MapEntry *e) {
	MapFindResult fr = {-1, -1, -1};
	if (buf_len(m->hashes) > 0) {
		fr.hash_index = e->key.key % cast(u64)buf_len(m->hashes);
		fr.entry_index = m->hashes[fr.hash_index];
		while (fr.entry_index >= 0) {
			if (&m->entries[fr.entry_index] == e) {
				return fr;
			}
			fr.entry_prev = fr.entry_index;
			fr.entry_index = m->entries[fr.entry_index].next;
		}
	}
	return fr;
}

bool map__full(Map *m) {
	return 0.75 * buf_len(m->hashes) <= buf_len(m->entries);
}


#define MAP_ARRAY_GROW_FORMULA(x) (4*(x) + 7)
void map_grow(Map *m) {
	isize new_count = MAP_ARRAY_GROW_FORMULA(buf_len(m->entries));
	map_rehash(m, new_count);
}


void map_rehash(Map *m, isize new_count) {
	isize i, j;
	Map nm = {0};
	map_init(&nm);
	buf_resize(nm.hashes, new_count);
	buf_reserve(nm.entries, buf_len(m->entries));
	for (i = 0; i < new_count; i++) {
		nm.hashes[i] = -1;
	}
	for (i = 0; i < buf_len(m->entries); i++) {
		MapEntry *e = &m->entries[i];
		MapFindResult fr;
		if (buf_len(nm.hashes) == 0) {
			map_grow(&nm);
		}
		fr = map__find(&nm, e->key);
		j = map__add_entry(&nm, e->key);
		if (fr.entry_prev < 0) {
			nm.hashes[fr.hash_index] = j;
		} else {
			nm.entries[fr.entry_prev].next = j;
		}
		nm.entries[j].next = fr.entry_index;
		nm.entries[j].value = e->value;
		if (map__full(&nm)) {
			map_grow(&nm);
		}
	}
	map_destroy(m);
	*m = nm;
}


bool map_exists(Map *m, HashKey key) {
	isize index = map__find(m, key).entry_index;
	return index >= 0;
}


void *map_get(Map *m, HashKey key) {
	isize index = map__find(m, key).entry_index;
	if (index >= 0) {
		return m->entries[index].value;
	}
	return NULL;
}

void map_set(Map *m, HashKey key, void *value) {
	isize index;
	MapFindResult fr;
	if (buf_len(m->hashes) == 0) {
		map_grow(m);
	}
	fr = map__find(m, key);
	if (fr.entry_index >= 0) {
		index = fr.entry_index;
	} else {
		index = map__add_entry(m, key);
		if (fr.entry_prev >= 0) {
			m->entries[fr.entry_prev].next = index;
		} else {
			m->hashes[fr.hash_index] = index;
		}
	}
	m->entries[index].value = value;

	if (map__full(m)) {
		map_grow(m);
	}
}

void map_remove(Map *m, HashKey key) {
	MapFindResult fr = map__find(m, key);
	if (fr.entry_index >= 0) {
		isize n;
		MapFindResult last;
		if (fr.entry_prev < 0) {
			m->hashes[fr.hash_index] = m->entries[fr.entry_index].next;
		} else {
			m->entries[fr.entry_prev].next = m->entries[fr.entry_index].next;
		}

		n = buf_len(m->entries);
		if (fr.entry_index == n-1) {
			buf_pop(m->entries);
			return;
		}
		m->entries[fr.entry_index] = m->entries[n-1];
		last = map__find(m, m->entries[fr.entry_index].key);
		if (last.entry_prev >= 0) {
			m->entries[last.entry_prev].next = fr.entry_index;
		} else {
			m->hashes[last.hash_index] = fr.entry_index;
		}
	}
}

void map_clear(Map *m) {
	buf_clear(m->hashes);
	buf_clear(m->entries);
}



