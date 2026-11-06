00000000000a1be4 <__strftime_fmt_1>:
   a1be4:	fc010113          	addi	sp,sp,-64
   a1be8:	02113c23          	sd	ra,56(sp)
   a1bec:	02813823          	sd	s0,48(sp)
   a1bf0:	02913423          	sd	s1,40(sp)
   a1bf4:	03213023          	sd	s2,32(sp)
   a1bf8:	01313c23          	sd	s3,24(sp)
   a1bfc:	01413823          	sd	s4,16(sp)
   a1c00:	01513423          	sd	s5,8(sp)
   a1c04:	00058413          	mv	s0,a1
   a1c08:	00050493          	mv	s1,a0
   a1c0c:	fdb60593          	addi	a1,a2,-37
   a1c10:	05500813          	li	a6,85
   a1c14:	00000513          	li	a0,0
   a1c18:	5cb86063          	bltu	a6,a1,a21d8 <__strftime_fmt_1+0x5f4>
   a1c1c:	fff70817          	auipc	a6,0xfff70
   a1c20:	00259593          	slli	a1,a1,0x2
   a1c24:	fff81897          	auipc	a7,0xfff81
   a1c28:	dd088293          	addi	t0,a7,-560 # 229f4 <__month_to_secs.secs_through_month+0x30>
   a1c2c:	005585b3          	add	a1,a1,t0
   a1c30:	0005a583          	lw	a1,0(a1)
   a1c34:	81280813          	addi	a6,a6,-2030 # 1142e <__global_pointer$+0xc2e>
   a1c38:	03000893          	li	a7,48
   a1c3c:	00020337          	lui	t1,0x20
   a1c40:	005583b3          	add	t2,a1,t0
   a1c44:	0283059b          	addiw	a1,t1,40 # 20028 <__global_pointer$+0xf828>
   a1c48:	00038067          	jr	t2
   a1c4c:	0146a903          	lw	s2,20(a3)
   a1c50:	01c6a503          	lw	a0,28(a3)
   a1c54:	00200593          	li	a1,2
   a1c58:	76c90713          	addi	a4,s2,1900
   a1c5c:	04a5c263          	blt	a1,a0,a1ca0 <__strftime_fmt_1+0xbc>
   a1c60:	00060993          	mv	s3,a2
   a1c64:	00078a13          	mv	s4,a5
   a1c68:	00068513          	mv	a0,a3
   a1c6c:	00070a93          	mv	s5,a4
   a1c70:	598000ef          	jal	a2208 <week_num>
   a1c74:	000a8713          	mv	a4,s5
   a1c78:	00100593          	li	a1,1
   a1c7c:	4cb50063          	beq	a0,a1,a213c <__strftime_fmt_1+0x558>
   a1c80:	76b90713          	addi	a4,s2,1899
   a1c84:	4b80006f          	j	a213c <__strftime_fmt_1+0x558>
   a1c88:	0106a503          	lw	a0,16(a3)
   a1c8c:	00b00593          	li	a1,11
   a1c90:	04a5f063          	bgeu	a1,a0,a1cd0 <__strftime_fmt_1+0xec>
   a1c94:	fff7b517          	auipc	a0,0xfff7b
   a1c98:	fd950493          	addi	s1,a0,-39 # 1cc6d <__global_pointer$+0xc46d>
   a1c9c:	4580006f          	j	a20f4 <__strftime_fmt_1+0x510>
   a1ca0:	16900593          	li	a1,361
   a1ca4:	4ab56063          	bltu	a0,a1,a2144 <__strftime_fmt_1+0x560>
   a1ca8:	00060993          	mv	s3,a2
   a1cac:	00070a93          	mv	s5,a4
   a1cb0:	00078a13          	mv	s4,a5
   a1cb4:	00068513          	mv	a0,a3
   a1cb8:	550000ef          	jal	a2208 <week_num>
   a1cbc:	00100593          	li	a1,1
   a1cc0:	46b50c63          	beq	a0,a1,a2138 <__strftime_fmt_1+0x554>
   a1cc4:	000a0793          	mv	a5,s4
   a1cc8:	000a8713          	mv	a4,s5
   a1ccc:	4740006f          	j	a2140 <__strftime_fmt_1+0x55c>
   a1cd0:	000205b7          	lui	a1,0x20
   a1cd4:	00758593          	addi	a1,a1,7 # 20007 <__global_pointer$+0xf807>
   a1cd8:	00b50533          	add	a0,a0,a1
   a1cdc:	0075051b          	addiw	a0,a0,7
   a1ce0:	4080006f          	j	a20e8 <__strftime_fmt_1+0x504>
   a1ce4:	0146a503          	lw	a0,20(a3)
   a1ce8:	fff6e597          	auipc	a1,0xfff6e
   a1cec:	6185b583          	ld	a1,1560(a1) # 10300 <rt_0+0x102f0>
   a1cf0:	76c50513          	addi	a0,a0,1900
   a1cf4:	02b515b3          	mulh	a1,a0,a1
   a1cf8:	00a585b3          	add	a1,a1,a0
   a1cfc:	03f5d613          	srli	a2,a1,0x3f
   a1d00:	4065d593          	srai	a1,a1,0x6
   a1d04:	00c585b3          	add	a1,a1,a2
   a1d08:	06400613          	li	a2,100
   a1d0c:	02c585b3          	mul	a1,a1,a2
   a1d10:	03000893          	li	a7,48
   a1d14:	40b50533          	sub	a0,a0,a1
   a1d18:	43f55593          	srai	a1,a0,0x3f
   a1d1c:	00b54533          	xor	a0,a0,a1
   a1d20:	40b50733          	sub	a4,a0,a1
   a1d24:	4540006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1d28:	00020537          	lui	a0,0x20
   a1d2c:	02a5059b          	addiw	a1,a0,42 # 2002a <__global_pointer$+0xf82a>
   a1d30:	3240006f          	j	a2054 <__strftime_fmt_1+0x470>
   a1d34:	05f00893          	li	a7,95
   a1d38:	00c6a703          	lw	a4,12(a3)
   a1d3c:	43c0006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1d40:	0186a503          	lw	a0,24(a3)
   a1d44:	00600593          	li	a1,6
   a1d48:	36a5f263          	bgeu	a1,a0,a20ac <__strftime_fmt_1+0x4c8>
   a1d4c:	fff7b517          	auipc	a0,0xfff7b
   a1d50:	f2150493          	addi	s1,a0,-223 # 1cc6d <__global_pointer$+0xc46d>
   a1d54:	3a00006f          	j	a20f4 <__strftime_fmt_1+0x510>
   a1d58:	fff7e517          	auipc	a0,0xfff7e
   a1d5c:	58c50813          	addi	a6,a0,1420 # 202e4 <__global_pointer$+0xfae4>
   a1d60:	3140006f          	j	a2074 <__strftime_fmt_1+0x490>
   a1d64:	0186a703          	lw	a4,24(a3)
   a1d68:	22071463          	bnez	a4,a1f90 <__strftime_fmt_1+0x3ac>
   a1d6c:	00700713          	li	a4,7
   a1d70:	2200006f          	j	a1f90 <__strftime_fmt_1+0x3ac>
   a1d74:	0046a703          	lw	a4,4(a3)
   a1d78:	03000893          	li	a7,48
   a1d7c:	3fc0006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1d80:	00100513          	li	a0,1
   a1d84:	00a43023          	sd	a0,0(s0)
   a1d88:	fff79517          	auipc	a0,0xfff79
   a1d8c:	97c50513          	addi	a0,a0,-1668 # 1a704 <__global_pointer$+0x9f04>
   a1d90:	4480006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a1d94:	0086a503          	lw	a0,8(a3)
   a1d98:	000205b7          	lui	a1,0x20
   a1d9c:	00c52513          	slti	a0,a0,12
   a1da0:	00154513          	xori	a0,a0,1
   a1da4:	0265859b          	addiw	a1,a1,38 # 20026 <__global_pointer$+0xf826>
   a1da8:	3080006f          	j	a20b0 <__strftime_fmt_1+0x4cc>
   a1dac:	00068513          	mv	a0,a3
   a1db0:	00078913          	mv	s2,a5
   a1db4:	00068993          	mv	s3,a3
   a1db8:	d25ff0ef          	jal	a1adc <__tm_to_secs>
   a1dbc:	00090793          	mv	a5,s2
   a1dc0:	0289b583          	ld	a1,40(s3)
   a1dc4:	03000893          	li	a7,48
   a1dc8:	40b50733          	sub	a4,a0,a1
   a1dcc:	00100693          	li	a3,1
   a1dd0:	3a090a63          	beqz	s2,a2184 <__strftime_fmt_1+0x5a0>
   a1dd4:	3ac0006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a1dd8:	0006a703          	lw	a4,0(a3)
   a1ddc:	03000893          	li	a7,48
   a1de0:	3980006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1de4:	0146a503          	lw	a0,20(a3)
   a1de8:	000025b7          	lui	a1,0x2
   a1dec:	fa45859b          	addiw	a1,a1,-92 # 1fa4 <rt_0+0x1f94>
   a1df0:	76c50713          	addi	a4,a0,1900
   a1df4:	2cb54263          	blt	a0,a1,a20b8 <__strftime_fmt_1+0x4d4>
   a1df8:	fff74517          	auipc	a0,0xfff74
   a1dfc:	22050613          	addi	a2,a0,544 # 16018 <__global_pointer$+0x5818>
   a1e00:	39c0006f          	j	a219c <__strftime_fmt_1+0x5b8>
   a1e04:	fff73517          	auipc	a0,0xfff73
   a1e08:	23150813          	addi	a6,a0,561 # 15035 <__global_pointer$+0x4835>
   a1e0c:	2680006f          	j	a2074 <__strftime_fmt_1+0x490>
   a1e10:	fff70517          	auipc	a0,0xfff70
   a1e14:	e0150813          	addi	a6,a0,-511 # 11c11 <__global_pointer$+0x1411>
   a1e18:	25c0006f          	j	a2074 <__strftime_fmt_1+0x490>
   a1e1c:	0106a503          	lw	a0,16(a3)
   a1e20:	00b00593          	li	a1,11
   a1e24:	2aa5f263          	bgeu	a1,a0,a20c8 <__strftime_fmt_1+0x4e4>
   a1e28:	fff7b517          	auipc	a0,0xfff7b
   a1e2c:	e4550493          	addi	s1,a0,-443 # 1cc6d <__global_pointer$+0xc46d>
   a1e30:	2c40006f          	j	a20f4 <__strftime_fmt_1+0x510>
   a1e34:	00020537          	lui	a0,0x20
   a1e38:	02b5059b          	addiw	a1,a0,43 # 2002b <__global_pointer$+0xf82b>
   a1e3c:	2180006f          	j	a2054 <__strftime_fmt_1+0x470>
   a1e40:	0206a503          	lw	a0,32(a3)
   a1e44:	2c054463          	bltz	a0,a210c <__strftime_fmt_1+0x528>
   a1e48:	0286b503          	ld	a0,40(a3)
   a1e4c:	fff6e597          	auipc	a1,0xfff6e
   a1e50:	4cc5b583          	ld	a1,1228(a1) # 10318 <rt_0+0x10308>
   a1e54:	06400613          	li	a2,100
   a1e58:	02b515b3          	mulh	a1,a0,a1
   a1e5c:	03f5d693          	srli	a3,a1,0x3f
   a1e60:	40a5d593          	srai	a1,a1,0xa
   a1e64:	00d585b3          	add	a1,a1,a3
   a1e68:	000016b7          	lui	a3,0x1
   a1e6c:	e106869b          	addiw	a3,a3,-496 # e10 <rt_0+0xe00>
   a1e70:	02c58633          	mul	a2,a1,a2
   a1e74:	02d585b3          	mul	a1,a1,a3
   a1e78:	ffff96b7          	lui	a3,0xffff9
   a1e7c:	8896869b          	addiw	a3,a3,-1911 # ffffffffffff8889 <r1+0xffffffffff9e34cd>
   a1e80:	40b50533          	sub	a0,a0,a1
   a1e84:	02d505b3          	mul	a1,a0,a3
   a1e88:	0105d593          	srli	a1,a1,0x10
   a1e8c:	00a58533          	add	a0,a1,a0
   a1e90:	03051513          	slli	a0,a0,0x30
   a1e94:	03f55593          	srli	a1,a0,0x3f
   a1e98:	43555513          	srai	a0,a0,0x35
   a1e9c:	00b50533          	add	a0,a0,a1
   a1ea0:	00a606b3          	add	a3,a2,a0
   a1ea4:	fff77517          	auipc	a0,0xfff77
   a1ea8:	07650613          	addi	a2,a0,118 # 18f1a <__global_pointer$+0x871a>
   a1eac:	06400593          	li	a1,100
   a1eb0:	00048513          	mv	a0,s1
   a1eb4:	2f40006f          	j	a21a8 <__strftime_fmt_1+0x5c4>
   a1eb8:	0186a503          	lw	a0,24(a3)
   a1ebc:	01c6a583          	lw	a1,28(a3)
   a1ec0:	24925637          	lui	a2,0x24925
   a1ec4:	92560613          	addi	a2,a2,-1755 # 24924925 <r1+0x2430f569>
   a1ec8:	02061613          	slli	a2,a2,0x20
   a1ecc:	40a585bb          	subw	a1,a1,a0
   a1ed0:	00758593          	addi	a1,a1,7
   a1ed4:	02059513          	slli	a0,a1,0x20
   a1ed8:	02c53533          	mulhu	a0,a0,a2
   a1edc:	03000893          	li	a7,48
   a1ee0:	1180006f          	j	a1ff8 <__strftime_fmt_1+0x414>
   a1ee4:	00100513          	li	a0,1
   a1ee8:	00a43023          	sd	a0,0(s0)
   a1eec:	fff70517          	auipc	a0,0xfff70
   a1ef0:	41e50513          	addi	a0,a0,1054 # 1230a <__global_pointer$+0x1b0a>
   a1ef4:	2e40006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a1ef8:	00068513          	mv	a0,a3
   a1efc:	00078913          	mv	s2,a5
   a1f00:	308000ef          	jal	a2208 <week_num>
   a1f04:	00090793          	mv	a5,s2
   a1f08:	00050713          	mv	a4,a0
   a1f0c:	03000893          	li	a7,48
   a1f10:	2680006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1f14:	0186a503          	lw	a0,24(a3)
   a1f18:	00600593          	li	a1,6
   a1f1c:	1ca5f063          	bgeu	a1,a0,a20dc <__strftime_fmt_1+0x4f8>
   a1f20:	fff7b517          	auipc	a0,0xfff7b
   a1f24:	d4d50493          	addi	s1,a0,-691 # 1cc6d <__global_pointer$+0xc46d>
   a1f28:	1cc0006f          	j	a20f4 <__strftime_fmt_1+0x510>
   a1f2c:	0086a703          	lw	a4,8(a3)
   a1f30:	03000893          	li	a7,48
   a1f34:	00200693          	li	a3,2
   a1f38:	1e070263          	beqz	a4,a211c <__strftime_fmt_1+0x538>
   a1f3c:	00d72513          	slti	a0,a4,13
   a1f40:	fff50513          	addi	a0,a0,-1
   a1f44:	ff457513          	andi	a0,a0,-12
   a1f48:	00a70733          	add	a4,a4,a0
   a1f4c:	22078c63          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a1f50:	2300006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a1f54:	0146a503          	lw	a0,20(a3)
   a1f58:	fff6e597          	auipc	a1,0xfff6e
   a1f5c:	3a85b583          	ld	a1,936(a1) # 10300 <rt_0+0x102f0>
   a1f60:	03000893          	li	a7,48
   a1f64:	76c50513          	addi	a0,a0,1900
   a1f68:	02b515b3          	mulh	a1,a0,a1
   a1f6c:	00a58533          	add	a0,a1,a0
   a1f70:	03f55713          	srli	a4,a0,0x3f
   a1f74:	40655513          	srai	a0,a0,0x6
   a1f78:	00e50733          	add	a4,a0,a4
   a1f7c:	1fc0006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1f80:	0086a703          	lw	a4,8(a3)
   a1f84:	03000893          	li	a7,48
   a1f88:	1f00006f          	j	a2178 <__strftime_fmt_1+0x594>
   a1f8c:	0186a703          	lw	a4,24(a3)
   a1f90:	03000893          	li	a7,48
   a1f94:	00100693          	li	a3,1
   a1f98:	1e078663          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a1f9c:	1e40006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a1fa0:	0186a503          	lw	a0,24(a3)
   a1fa4:	01c6a583          	lw	a1,28(a3)
   a1fa8:	24925637          	lui	a2,0x24925
   a1fac:	9256061b          	addiw	a2,a2,-1755 # 24924925 <r1+0x2430f569>
   a1fb0:	00650513          	addi	a0,a0,6
   a1fb4:	02051693          	slli	a3,a0,0x20
   a1fb8:	0206d693          	srli	a3,a3,0x20
   a1fbc:	02c686b3          	mul	a3,a3,a2
   a1fc0:	0206d693          	srli	a3,a3,0x20
   a1fc4:	40d5073b          	subw	a4,a0,a3
   a1fc8:	0017571b          	srliw	a4,a4,0x1
   a1fcc:	00d706b3          	add	a3,a4,a3
   a1fd0:	03000893          	li	a7,48
   a1fd4:	0026d693          	srli	a3,a3,0x2
   a1fd8:	00a68533          	add	a0,a3,a0
   a1fdc:	00369693          	slli	a3,a3,0x3
   a1fe0:	40a686bb          	subw	a3,a3,a0
   a1fe4:	00d585b3          	add	a1,a1,a3
   a1fe8:	00758593          	addi	a1,a1,7
   a1fec:	02059513          	slli	a0,a1,0x20
   a1ff0:	02055513          	srli	a0,a0,0x20
   a1ff4:	02c50533          	mul	a0,a0,a2
   a1ff8:	02055513          	srli	a0,a0,0x20
   a1ffc:	40a585bb          	subw	a1,a1,a0
   a2000:	0015d59b          	srliw	a1,a1,0x1
   a2004:	00a58533          	add	a0,a1,a0
   a2008:	00255713          	srli	a4,a0,0x2
   a200c:	16c0006f          	j	a2178 <__strftime_fmt_1+0x594>
   a2010:	0206a503          	lw	a0,32(a3)
   a2014:	10054a63          	bltz	a0,a2128 <__strftime_fmt_1+0x544>
   a2018:	00068513          	mv	a0,a3
   a201c:	935fe0ef          	jal	a0950 <__tm_to_tzname>
   a2020:	0d00006f          	j	a20f0 <__strftime_fmt_1+0x50c>
   a2024:	0106a703          	lw	a4,16(a3)
   a2028:	03000893          	li	a7,48
   a202c:	00170713          	addi	a4,a4,1
   a2030:	1480006f          	j	a2178 <__strftime_fmt_1+0x594>
   a2034:	01c6a703          	lw	a4,28(a3)
   a2038:	03000893          	li	a7,48
   a203c:	00170713          	addi	a4,a4,1
   a2040:	00300693          	li	a3,3
   a2044:	14078063          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a2048:	1380006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a204c:	00020537          	lui	a0,0x20
   a2050:	0295059b          	addiw	a1,a0,41 # 20029 <__global_pointer$+0xf829>
   a2054:	00058513          	mv	a0,a1
   a2058:	00070593          	mv	a1,a4
   a205c:	00068913          	mv	s2,a3
   a2060:	00070993          	mv	s3,a4
   a2064:	fe5fd0ef          	jal	a0048 <__nl_langinfo_l>
   a2068:	00098713          	mv	a4,s3
   a206c:	00090693          	mv	a3,s2
   a2070:	00050813          	mv	a6,a0
   a2074:	06400593          	li	a1,100
   a2078:	00048513          	mv	a0,s1
   a207c:	00080613          	mv	a2,a6
   a2080:	3f0000ef          	jal	a2470 <strftime_l>
   a2084:	00a43023          	sd	a0,0(s0)
   a2088:	00153513          	seqz	a0,a0
   a208c:	fff50513          	addi	a0,a0,-1
   a2090:	00957533          	and	a0,a0,s1
   a2094:	1440006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a2098:	00100513          	li	a0,1
   a209c:	00a43023          	sd	a0,0(s0)
   a20a0:	fff76517          	auipc	a0,0xfff76
   a20a4:	eda50513          	addi	a0,a0,-294 # 17f7a <__global_pointer$+0x777a>
   a20a8:	1300006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a20ac:	000205b7          	lui	a1,0x20
   a20b0:	00b56533          	or	a0,a0,a1
   a20b4:	0340006f          	j	a20e8 <__strftime_fmt_1+0x504>
   a20b8:	03000893          	li	a7,48
   a20bc:	00400693          	li	a3,4
   a20c0:	0c078263          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a20c4:	0bc0006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a20c8:	000205b7          	lui	a1,0x20
   a20cc:	00758593          	addi	a1,a1,7 # 20007 <__global_pointer$+0xf807>
   a20d0:	00b50533          	add	a0,a0,a1
   a20d4:	0135051b          	addiw	a0,a0,19
   a20d8:	0100006f          	j	a20e8 <__strftime_fmt_1+0x504>
   a20dc:	000205b7          	lui	a1,0x20
   a20e0:	00758593          	addi	a1,a1,7 # 20007 <__global_pointer$+0xf807>
   a20e4:	00b5053b          	addw	a0,a0,a1
   a20e8:	00070593          	mv	a1,a4
   a20ec:	f5dfd0ef          	jal	a0048 <__nl_langinfo_l>
   a20f0:	00050493          	mv	s1,a0
   a20f4:	00048513          	mv	a0,s1
   a20f8:	be5a00ef          	jal	42cdc <wrapper_strlen>
   a20fc:	00050593          	mv	a1,a0
   a2100:	00048513          	mv	a0,s1
   a2104:	00b43023          	sd	a1,0(s0)
   a2108:	0d00006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a210c:	00043023          	sd	zero,0(s0)
   a2110:	fff72517          	auipc	a0,0xfff72
   a2114:	e0850513          	addi	a0,a0,-504 # 13f18 <__global_pointer$+0x3718>
   a2118:	0c00006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a211c:	00c00713          	li	a4,12
   a2120:	06078263          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a2124:	05c0006f          	j	a2180 <__strftime_fmt_1+0x59c>
   a2128:	00043023          	sd	zero,0(s0)
   a212c:	fff72517          	auipc	a0,0xfff72
   a2130:	dec50513          	addi	a0,a0,-532 # 13f18 <__global_pointer$+0x3718>
   a2134:	0a40006f          	j	a21d8 <__strftime_fmt_1+0x5f4>
   a2138:	76d90713          	addi	a4,s2,1901
   a213c:	000a0793          	mv	a5,s4
   a2140:	00098613          	mv	a2,s3
   a2144:	06700513          	li	a0,103
   a2148:	03000893          	li	a7,48
   a214c:	0aa61863          	bne	a2,a0,a21fc <__strftime_fmt_1+0x618>
   a2150:	fff6e517          	auipc	a0,0xfff6e
   a2154:	1b053503          	ld	a0,432(a0) # 10300 <rt_0+0x102f0>
   a2158:	02a71533          	mulh	a0,a4,a0
   a215c:	00e50533          	add	a0,a0,a4
   a2160:	03f55593          	srli	a1,a0,0x3f
   a2164:	40655513          	srai	a0,a0,0x6
   a2168:	00b50533          	add	a0,a0,a1
   a216c:	06400593          	li	a1,100
   a2170:	02b50533          	mul	a0,a0,a1
   a2174:	40a70733          	sub	a4,a4,a0
   a2178:	00200693          	li	a3,2
   a217c:	00078463          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a2180:	00078893          	mv	a7,a5
   a2184:	05f00513          	li	a0,95
   a2188:	02a88463          	beq	a7,a0,a21b0 <__strftime_fmt_1+0x5cc>
   a218c:	02d00513          	li	a0,45
   a2190:	02a89663          	bne	a7,a0,a21bc <__strftime_fmt_1+0x5d8>
   a2194:	fff70517          	auipc	a0,0xfff70
   a2198:	2fd50613          	addi	a2,a0,765 # 12491 <__global_pointer$+0x1c91>
   a219c:	06400593          	li	a1,100
   a21a0:	00048513          	mv	a0,s1
   a21a4:	00070693          	mv	a3,a4
   a21a8:	b75a00ef          	jal	42d1c <wrapper_snprintf>
   a21ac:	0240006f          	j	a21d0 <__strftime_fmt_1+0x5ec>
   a21b0:	fff7e517          	auipc	a0,0xfff7e
   a21b4:	64d50613          	addi	a2,a0,1613 # 207fd <__global_pointer$+0xfffd>
   a21b8:	00c0006f          	j	a21c4 <__strftime_fmt_1+0x5e0>
   a21bc:	fff79517          	auipc	a0,0xfff79
   a21c0:	e1f50613          	addi	a2,a0,-481 # 1afdb <__global_pointer$+0xa7db>
   a21c4:	06400593          	li	a1,100
   a21c8:	00048513          	mv	a0,s1
   a21cc:	b51a00ef          	jal	42d1c <wrapper_snprintf>
   a21d0:	00a43023          	sd	a0,0(s0)
   a21d4:	00048513          	mv	a0,s1
   a21d8:	03813083          	ld	ra,56(sp)
   a21dc:	03013403          	ld	s0,48(sp)
   a21e0:	02813483          	ld	s1,40(sp)
   a21e4:	02013903          	ld	s2,32(sp)
   a21e8:	01813983          	ld	s3,24(sp)
   a21ec:	01013a03          	ld	s4,16(sp)
   a21f0:	00813a83          	ld	s5,8(sp)
   a21f4:	04010113          	addi	sp,sp,64
   a21f8:	00008067          	ret
   a21fc:	00400693          	li	a3,4
   a2200:	f80782e3          	beqz	a5,a2184 <__strftime_fmt_1+0x5a0>
   a2204:	f7dff06f          	j	a2180 <__strftime_fmt_1+0x59c>
