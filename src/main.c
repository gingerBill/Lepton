#include "common.c"
#include "map.c"
#include "tokenizer.c"
#include "ast.c"
#include "parser.c"
#include "const_value.c"
#include "checker.c"


void print_usage(void) {
	fprintf(stderr, "lepton\n");
	fprintf(stderr, "\tbuild (arguments)\n");
}

int main(int argc, char **argv) {
	if (argc < 2) {
		print_usage();
		return 1;
	}
	if (strncmp(argv[1], "build", 5) != 0) {
		print_usage();
		return 1;
	}

	if (argc != 3) {
		print_usage();
		return 1;
	}

	init_universal_scope();

	{
		AstPackage *p = MEM_NEW(AstPackage);
		ParserError err = parse_package(p, argv[2]);
		if (err == ParserError_None) {
			Checker c = {0};
			checker_init(&c);
			check_package(&c, p);
		}
	}
	return 0;
}
