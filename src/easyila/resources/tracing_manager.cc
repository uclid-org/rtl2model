#include "tracing_manager.h"
#include "portconfig.h"

void TracingManager::gen_preamble (std::ofstream& file_) {
	file_ << "input-language Verilog\n";
	file_ << "decl-version 2.0\n";
	file_ << "var-comparability implicit\n";
}

void TracingManager::csv_gen_decls (std::ofstream& file_) {
	std::stringstream decls_names_;
	std::stringstream decls_width_;
	CSV_ADD_DECLS_STMTS
	file_ << decls_names_.rdbuf() << "\n";
	file_ << decls_width_.rdbuf() << "\n";
}

void TracingManager::gen_decls (std::ofstream& file_) {
	file_ << "input-language Verilog\n";
	file_ << "decl-version 2.0\n";
	file_ << "var-comparability implicit\n";
	file_ << "\n";
	
	file_ << "ppt Cycle:::ENTER\n";
	file_ << "  ppt-type enter\n";
	ADD_DECLS_STMTS
	file_ << "\n";

	file_ << "ppt Cycle:::EXIT0\n";
	file_ << "  ppt-type exit\n";
	ADD_DECLS_STMTS
	file_ << "\n";
}

void TracingManager::make_preamble () {
    gen_preamble(trace_file);
    gen_decls(decls_file);
}

void TracingManager::csv_make_preamble() {
	csv_gen_decls(trace_file);
}
