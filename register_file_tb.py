import cocotb
from cocotb.triggers import Timer, RisingEdge, FallingEdge
from cocotb.clock import Clock

async def reset(rst_n, duration_ns):
    rst_n.value = 0
    await Timer(duration_ns, units="ns")
    rst_n.value = 1


@cocotb.test()
async def reset_test(dut):
    i_clk, i_rst_n = dut.i_clk, dut.i_rst_n
    i_rs1, i_rs2, i_rd = dut.i_rs1, dut.i_rs2, dut.i_rd
    i_wen, i_wdata = dut.i_wen, dut.i_wdata
    o_rs1, o_rs2 = dut.o_rs1, dut.o_rs2

    # check reset
    async_reset = cocotb.start_soon(reset(i_rst_n, 500))
    await Timer(250, units="ns")
    assert o_rs1.value == 0
    assert o_rs2.value == 0


@cocotb.test()
async def zero_test(dut):
    i_clk, i_rst_n = dut.i_clk, dut.i_rst_n
    i_rs1, i_rs2, i_rd = dut.i_rs1, dut.i_rs2, dut.i_rd
    i_wen, i_wdata = dut.i_wen, dut.i_wdata
    o_rs1, o_rs2 = dut.o_rs1, dut.o_rs2

    await reset(i_rst_n, 500)
    cocotb.start_soon(Clock(i_clk, 1, units="ns").start())

    i_rs1.value = 0
    i_rs2.value = 0
    i_rd.value = 0

    i_wen.value = 0
    await FallingEdge(i_clk)
    assert o_rs1.value == 0
    assert o_rs2.value == 0

    i_wen.value = 1
    i_wdata.value = 0xcafe
    await FallingEdge(i_clk)
    assert o_rs1.value == 0
    assert o_rs2.value == 0


@cocotb.test()
async def rw_test(dut):
    i_clk, i_rst_n = dut.i_clk, dut.i_rst_n
    i_rs1, i_rs2, i_rd = dut.i_rs1, dut.i_rs2, dut.i_rd
    i_wen, i_wdata = dut.i_wen, dut.i_wdata
    o_rs1, o_rs2 = dut.o_rs1, dut.o_rs2

    await reset(i_rst_n, 500)
    cocotb.start_soon(Clock(i_clk, 1, units="ns").start())

    i_rd.value = 1
    i_wen.value = 1
    i_wdata.value = 0xcafe
    await FallingEdge(i_clk)

    i_rd.value = 2
    i_wen.value = 1
    i_wdata.value = 0xb0ba
    await FallingEdge(i_clk)

    i_rs1.value = 1
    i_rs2.value = 2
    i_wen.value = 0
    await FallingEdge(i_clk)
    assert o_rs1.value == 0xcafe
    assert o_rs2.value == 0xb0ba

    i_rd.value = 1
    i_wen.value = 0
    i_wdata.value = 0xb0ba
    await FallingEdge(i_clk)
    assert o_rs1.value == 0xcafe
    assert o_rs2.value == 0xb0ba

    for i in range(1, 32):
        i_rd.value = i
        i_wen.value = 1
        i_wdata.value = i * 1000
        await FallingEdge(i_clk)

    i_wen.value = 0
    for i in range(0, 32, 2):
        i_rs1.value = i
        i_rs2.value = i + 1
        await FallingEdge(i_clk)
        assert o_rs1.value == i * 1000
        assert o_rs2.value == (i + 1) * 1000
