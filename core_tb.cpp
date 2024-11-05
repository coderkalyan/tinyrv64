#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <verilated.h>
#include <verilated_vcd_c.h>

#include "Vcore.h"
#include "Vcore___024root.h"

void dump_rf(Vcore *dut) {
    std::cout << "register dump:" << std::endl;
    for (size_t i = 0; i < 32; i += 4) {
        for (size_t j = 0; j < 4; j++) {
            const size_t index = i + j;
            printf("x%02zu: 0x%016d ", index,
                   (index == 0) ? 0
                                : dut->rootp->core__DOT__rf__DOT__rdata[i - 1]);
        }
        printf("\n");
    }

    printf("\n");
}

int main(int argc, char *argv[]) {
    Vcore *dut = new Vcore;

    Verilated::traceEverOn(true);
    VerilatedVcdC *trace = new VerilatedVcdC;
    dut->trace(trace, 5);
    trace->open("waveform.vcd");

    vluint64_t sim_time = 0;

    std::cout << "resetting..." << std::endl;
    dut->i_rst_n = 0;
    dut->i_clk = 0;
    dut->eval();
    trace->dump(sim_time);
    sim_time += 1;

    dut->i_rst_n = 1;
    dut->i_imem_data = 0x3e800093;
    dut->eval();
    trace->dump(sim_time);
    sim_time += 1;
    dump_rf(dut);

    dut->i_clk = 1;
    dut->eval();
    trace->dump(sim_time);
    sim_time += 1;

    dut->i_clk = 0;
    dut->eval();
    trace->dump(sim_time);
    sim_time += 1;

    dut->i_clk = 0;
    dut->eval();
    trace->dump(sim_time);
    sim_time += 1;
    dump_rf(dut);

    trace->close();
    delete dut;
    exit(EXIT_SUCCESS);
}
