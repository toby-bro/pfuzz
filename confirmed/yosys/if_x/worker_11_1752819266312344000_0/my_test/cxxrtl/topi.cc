#include <cxxrtl/cxxrtl.h>

#if defined(CXXRTL_INCLUDE_CAPI_IMPL) || \
    defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi.cc>
#endif

#if defined(CXXRTL_INCLUDE_VCD_CAPI_IMPL)
#include <cxxrtl/capi/cxxrtl_capi_vcd.cc>
#endif

using namespace cxxrtl_yosys;

namespace cxxrtl_design {

// \top: 1
// \src: ../topi.sv:1.1-20.10
struct p_topi : public module {
	// \src: ../topi.sv:2.17-2.20
	/*input*/ value<1> p_clk;
	value<1> prev_p_clk;
	bool posedge_p_clk() const {
		return !prev_p_clk.slice<0>().val() && p_clk.slice<0>().val();
	}
	// \src: ../topi.sv:3.18-3.22
	/*output*/ wire<1> p_out2;
	// \src: ../topi.sv:6.11-6.13
	wire<1> p_q1;
	p_topi(interior) {}
	p_topi() {
		reset();
	};

	void reset() override;

	bool eval(performer *performer = nullptr) override;

	template<class ObserverT>
	bool commit(ObserverT &observer) {
		bool changed = false;
		prev_p_clk = p_clk;
		if (p_out2.commit(observer)) changed = true;
		if (p_q1.commit(observer)) changed = true;
		return changed;
	}

	bool commit() override {
		observer observer;
		return commit<>(observer);
	}

	void debug_eval();

	void debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs = {}) override;
}; // struct p_topi

void p_topi::reset() {
}

bool p_topi::eval(performer *performer) {
	bool converged = true;
	bool posedge_p_clk = this->posedge_p_clk();
	// \src: ../topi.sv:8.5-10.8
	// cell $procdff$9
	if (posedge_p_clk) {
		p_q1.next = value<1>{0u};
	}
	// cells $procdff$8 $procmux$6
	if (posedge_p_clk) {
		p_out2.next = (p_q1.curr ? value<1>{0x1u} : p_out2.curr);
	}
	return converged;
}

void p_topi::debug_eval() {
}

CXXRTL_EXTREMELY_COLD
void p_topi::debug_info(debug_items *items, debug_scopes *scopes, std::string path, metadata_map &&cell_attrs) {
	assert(path.empty() || path[path.size() - 1] == ' ');
	if (scopes) {
		scopes->add(path.empty() ? path : path.substr(0, path.size() - 1), "topi", metadata_map({
			{ "top", UINT64_C(1) },
			{ "src", "../topi.sv:1.1-20.10" },
		}), std::move(cell_attrs));
	}
	if (items) {
		items->add(path, "clk", "src\000s../topi.sv:2.17-2.20\000", p_clk, 0, debug_item::INPUT|debug_item::UNDRIVEN);
		items->add(path, "out2", "src\000s../topi.sv:3.18-3.22\000", p_out2, 0, debug_item::OUTPUT|debug_item::DRIVEN_SYNC);
		items->add(path, "q1", "src\000s../topi.sv:6.11-6.13\000", p_q1, 0, debug_item::DRIVEN_SYNC);
	}
}

} // namespace cxxrtl_design

extern "C"
cxxrtl_toplevel cxxrtl_design_create() {
	return new _cxxrtl_toplevel { std::unique_ptr<cxxrtl_design::p_topi>(new cxxrtl_design::p_topi) };
}
