#include "common.c"
#include "utf8.c"
#include "tokenizer.c"
#include "ast.c"
#include "parser.c"


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

	{
		Parser p = {0};
		ParserError err = init_parser(&p, argv[2]);
		if (!err) {
			for (;;) {
				AstDecl *decl = parse_decl(&p);
				if (decl == NULL) {
					break;
				}
			}
		}
	}
	return 0;
}
