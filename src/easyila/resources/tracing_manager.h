#include "portconfig.h"

#include <iostream>
#include <sstream>
#include <fstream>

#ifndef TRACING_MANAGER_H_
#define TRACING_MANAGER_H_


class tracing_manager
{
private:
    std::ofstream trace_file;
    std::ofstream decls_file;
    std::string trace_file_path;
    std::string decls_file_path;

    // Adds the preamble.
    void gen_preamble (std::ofstream& file_);
    // And for csv style traces
    void csv_gen_decls (std::ofstream& file_);
    // Generate the .dtrace file entries
    template <class T>
    void gen_state (T * top_, std::ofstream& file_, bool enter_);
    // And for csv style trace output
    template <class T>
    void csv_gen_state (T * top_, std::ofstream& file_);
    // Generate declarations for the .decl file
    void gen_decls (std::ofstream& file_);
public:
    tracing_manager (std::string trace_file_path_, std::string decls_file_path_) : 
        trace_file_path(trace_file_path_),
        decls_file_path(decls_file_path_)
    {
        trace_file.open (trace_file_path_);
        if (decls_file_path_ != "") {
            decls_file.open (decls_file_path_);
        }
    }
    
    ~tracing_manager() {
        if (trace_file.is_open()) trace_file.close();
        if (decls_file.is_open()) decls_file.close();
    }

    // Preamble for both .dtrace and .decl files
    void make_preamble();
    // Preamble if we want a csv file
    void csv_make_preamble();
    // Generate the .dtrace file entries
    template <class T>
    void state_snapshot (T * top_, bool enter_);
    template <class T>
    void csv_state_snapshot (T* top_);

};

// Generate the .dtrace file entries
template <class T>
void tracing_manager::gen_state (T * top_, std::ofstream& file_, bool enter_) {
	char buf[1024];
	file_ << "\n";
	if (enter_) {
		file_ << "Cycle:::ENTER\n";
	} else {
		file_ << "Cycle:::EXIT0\n";
	}
	ADD_DTRACE_STMTS
}

// Generate the .dtrace file entries
template <class T>
void tracing_manager::state_snapshot (T * top_, bool enter_) {
	gen_state(top_, trace_file, enter_);
}

// CSV style variable snapshot
// Required for filename indirection :/
template <class T>
void tracing_manager::csv_gen_state (T * top_, std::ofstream& file_) {
	char buf[1024];
    CSV_ADD_DTRACE_STMTS
    file_ << "\n";
}

template <class T>
void tracing_manager::csv_state_snapshot (T* top_) {
    csv_gen_state(top_, trace_file);
}

#endif // TRACING_MANAGER_H_