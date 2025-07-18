// Generated C++ testbench for CXXRTL
// Do not edit this file directly : edit the template in internal/testgen/testbenches.go and generator.go
#include "WiredNet.cc" // CXXRTL generated header for the module

#include <fstream>
#include <iostream>
#include <iomanip>
#include <cstdint>
#include <string>
#include <sstream>
#include <type_traits>

// Template helpers to detect and work with both value<> and wire<> types
template<typename T>
struct has_curr {
    template<typename U>
    static auto test(int) -> decltype(std::declval<U>().curr, std::true_type{});
    template<typename>
    static std::false_type test(...);
    using type = decltype(test<T>(0));
    static constexpr bool value = type::value;
};

// Helper function to get port value - works with both value<> and wire<>
template<typename T, typename PortType>
typename std::enable_if<has_curr<PortType>::value, T>::type
_get_port_value(const PortType& port) {
    return port.curr.template get<T>();
}

template<typename T, typename PortType>
typename std::enable_if<!has_curr<PortType>::value, T>::type
_get_port_value(const PortType& port) {
    return port.template get<T>();
}

// Helper function to get port bit - works with both value<> and wire<>
template<typename PortType>
typename std::enable_if<has_curr<PortType>::value, bool>::type
_get_port_value(const PortType& port, int bit) {
    return port.curr.bit(bit);
}

template<typename PortType>
typename std::enable_if<!has_curr<PortType>::value, bool>::type
_get_port_value(const PortType& port, int bit) {
    return port.bit(bit);
}

// Helper function to get wide port value - works with both value<> and wire<>
template<typename PortType>
auto _get_port_value_wide(const PortType& port) -> typename std::enable_if<has_curr<PortType>::value, decltype(port.curr)>::type {
    return port.curr;
}

template<typename PortType>
auto _get_port_value_wide(const PortType& port) -> typename std::enable_if<!has_curr<PortType>::value, PortType>::type {
    return port;
}

// Helper function to set port value - works with both value<> and wire<>
template<typename T, typename PortType>
typename std::enable_if<has_curr<PortType>::value, void>::type
_set_port_value(PortType& port, T value) {
    port.next.template set<T>(value);
}

template<typename T, typename PortType>
typename std::enable_if<!has_curr<PortType>::value, void>::type
_set_port_value(PortType& port, T value) {
    port.template set<T>(value);
}

// Helper function to set wide port value - works with both value<> and wire<>
template<typename PortType, typename ValueType>
typename std::enable_if<has_curr<PortType>::value, void>::type
_set_port_value_wide(PortType& port, const ValueType& value) {
    port.next = value;
}

template<typename PortType, typename ValueType>
typename std::enable_if<!has_curr<PortType>::value, void>::type
_set_port_value_wide(PortType& port, const ValueType& value) {
    port = value;
}

int main(int argc, char** argv) {
    cxxrtl_design::p_WiredNet WiredNet_i; // DUT instance

    // Declare input variables
    bool data1;
    bool data2;


    // Read input values
    std::ifstream data1_file("input_data1.hex");
    if (!data1_file.is_open()) {
        std::cerr << "Failed to open input file for data1: input_data1.hex" << std::endl;
        return 1;
    }
    std::string data1_hex_str;
    data1_file >> data1_hex_str;
    if (data1_file.fail() && !data1_file.eof()) {
        std::cerr << "Failed to read hex string for data1 from input file: input_data1.hex" << std::endl;
        data1_file.close();
        return 1;
    }
    std::stringstream ss_data1;
    ss_data1 << std::hex << data1_hex_str;
    unsigned int temp_data1;
    if (!(ss_data1 >> temp_data1)) {
        std::cerr << "Failed to parse hex value for data1: " << data1_hex_str << std::endl;
        data1_file.close();
        return 1;
    }
    data1 = static_cast<bool>(temp_data1);
    data1_file.close();

    std::ifstream data2_file("input_data2.hex");
    if (!data2_file.is_open()) {
        std::cerr << "Failed to open input file for data2: input_data2.hex" << std::endl;
        return 1;
    }
    std::string data2_hex_str;
    data2_file >> data2_hex_str;
    if (data2_file.fail() && !data2_file.eof()) {
        std::cerr << "Failed to read hex string for data2 from input file: input_data2.hex" << std::endl;
        data2_file.close();
        return 1;
    }
    std::stringstream ss_data2;
    ss_data2 << std::hex << data2_hex_str;
    unsigned int temp_data2;
    if (!(ss_data2 >> temp_data2)) {
        std::cerr << "Failed to parse hex value for data2: " << data2_hex_str << std::endl;
        data2_file.close();
        return 1;
    }
    data2 = static_cast<bool>(temp_data2);
    data2_file.close();



    // Apply inputs to DUT
    _set_port_value<bool>(WiredNet_i.p_data1, data1);
    _set_port_value<bool>(WiredNet_i.p_data2, data2);
    // Input application


    // Handle reset, clock toggling, and evaluation

    // No clock found, performing bounded steps for combinational logic to settle
    for (int settle_step = 0; settle_step < 20; settle_step++) {
        WiredNet_i.step();
    }


    // Write outputs from DUT
    std::ofstream out_wired_file("output_out_wired.hex");
    if (!out_wired_file.is_open()) {
        std::cerr << "Failed to open output file for out_wired: output_out_wired.hex" << std::endl;
        return 1;
    }
    out_wired_file << (_get_port_value(WiredNet_i.p_out__wired, 0) ? '1' : '0') << std::endl;
    out_wired_file.close();



    return 0;
}
