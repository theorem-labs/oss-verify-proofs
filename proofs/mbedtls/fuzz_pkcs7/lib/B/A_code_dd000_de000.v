(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_dd000 : bv 32 := 0x1c853c87.

(* [comment removed for export] *)
Definition W_dd004 : bv 32 := 0x1d053d07.

(* [comment removed for export] *)
Definition W_dd008 : bv 32 := 0x1d853d87.

(* [comment removed for export] *)
Definition W_dd00c : bv 32 := 0x1e053e07.

(* [comment removed for export] *)
Definition W_dd010 : bv 32 := 0x1e853e87.

(* [comment removed for export] *)
Definition W_dd014 : bv 32 := 0x1f053f07.

(* [comment removed for export] *)
Definition W_dd018 : bv 32 := 0x1f853f87.

(* [comment removed for export] *)
Definition W_dd01c : bv 32 := 0x00053083.

(* [comment removed for export] *)
Definition W_dd020 : bv 32 := 0x01053103.

(* [comment removed for export] *)
Definition W_dd024 : bv 32 := 0x01853183.

(* [comment removed for export] *)
Definition W_dd028 : bv 32 := 0x02053203.

(* [comment removed for export] *)
Definition W_dd02c : bv 32 := 0x02853283.

(* [comment removed for export] *)
Definition W_dd030 : bv 32 := 0x03053303.

(* [comment removed for export] *)
Definition W_dd034 : bv 32 := 0x03853383.

(* [comment removed for export] *)
Definition W_dd038 : bv 32 := 0x04053403.

(* [comment removed for export] *)
Definition W_dd03c : bv 32 := 0x04853483.

(* [comment removed for export] *)
Definition W_dd040 : bv 32 := 0x05853583.

(* [comment removed for export] *)
Definition W_dd044 : bv 32 := 0x06053603.

(* [comment removed for export] *)
Definition W_dd048 : bv 32 := 0x06853683.

(* [comment removed for export] *)
Definition W_dd04c : bv 32 := 0x07053703.

(* [comment removed for export] *)
Definition W_dd050 : bv 32 := 0x07853783.

(* [comment removed for export] *)
Definition W_dd054 : bv 32 := 0x08053803.

(* [comment removed for export] *)
Definition W_dd058 : bv 32 := 0x08853883.

(* [comment removed for export] *)
Definition W_dd05c : bv 32 := 0x09053903.

(* [comment removed for export] *)
Definition W_dd060 : bv 32 := 0x09853983.

(* [comment removed for export] *)
Definition W_dd064 : bv 32 := 0x0a053a03.

(* [comment removed for export] *)
Definition W_dd068 : bv 32 := 0x0a853a83.

(* [comment removed for export] *)
Definition W_dd06c : bv 32 := 0x0b053b03.

(* [comment removed for export] *)
Definition W_dd070 : bv 32 := 0x0b853b83.

(* [comment removed for export] *)
Definition W_dd074 : bv 32 := 0x0c053c03.

(* [comment removed for export] *)
Definition W_dd078 : bv 32 := 0x0c853c83.

(* [comment removed for export] *)
Definition W_dd07c : bv 32 := 0x0d053d03.

(* [comment removed for export] *)
Definition W_dd080 : bv 32 := 0x0d853d83.

(* [comment removed for export] *)
Definition W_dd084 : bv 32 := 0x0e053e03.

(* [comment removed for export] *)
Definition W_dd088 : bv 32 := 0x0e853e83.

(* [comment removed for export] *)
Definition W_dd08c : bv 32 := 0x0f053f03.

(* [comment removed for export] *)
Definition W_dd090 : bv 32 := 0x0f853f83.

(* [comment removed for export] *)
Definition W_dd094 : bv 32 := 0x05053503.

(* [comment removed for export] *)
Definition W_dd098 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd09c : bv 32 := 0x00153023.

(* [comment removed for export] *)
Definition W_dd0a0 : bv 32 := 0x00153423.

(* [comment removed for export] *)
Definition W_dd0a4 : bv 32 := 0x00253823.

(* [comment removed for export] *)
Definition W_dd0a8 : bv 32 := 0x00353c23.

(* [comment removed for export] *)
Definition W_dd0ac : bv 32 := 0x02453023.

(* [comment removed for export] *)
Definition W_dd0b0 : bv 32 := 0x02553423.

(* [comment removed for export] *)
Definition W_dd0b4 : bv 32 := 0x02653823.

(* [comment removed for export] *)
Definition W_dd0b8 : bv 32 := 0x02753c23.

(* [comment removed for export] *)
Definition W_dd0bc : bv 32 := 0x04853023.

(* [comment removed for export] *)
Definition W_dd0c0 : bv 32 := 0x04953423.

(* [comment removed for export] *)
Definition W_dd0c4 : bv 32 := 0x04a53823.

(* [comment removed for export] *)
Definition W_dd0c8 : bv 32 := 0x04b53c23.

(* [comment removed for export] *)
Definition W_dd0cc : bv 32 := 0x06c53023.

(* [comment removed for export] *)
Definition W_dd0d0 : bv 32 := 0x06d53423.

(* [comment removed for export] *)
Definition W_dd0d4 : bv 32 := 0x06e53823.

(* [comment removed for export] *)
Definition W_dd0d8 : bv 32 := 0x06f53c23.

(* [comment removed for export] *)
Definition W_dd0dc : bv 32 := 0x09053023.

(* [comment removed for export] *)
Definition W_dd0e0 : bv 32 := 0x09153423.

(* [comment removed for export] *)
Definition W_dd0e4 : bv 32 := 0x09253823.

(* [comment removed for export] *)
Definition W_dd0e8 : bv 32 := 0x09353c23.

(* [comment removed for export] *)
Definition W_dd0ec : bv 32 := 0x0b453023.

(* [comment removed for export] *)
Definition W_dd0f0 : bv 32 := 0x0b553423.

(* [comment removed for export] *)
Definition W_dd0f4 : bv 32 := 0x0b653823.

(* [comment removed for export] *)
Definition W_dd0f8 : bv 32 := 0x0b753c23.

(* [comment removed for export] *)
Definition W_dd0fc : bv 32 := 0x0d853023.

(* [comment removed for export] *)
Definition W_dd100 : bv 32 := 0x0d953423.

(* [comment removed for export] *)
Definition W_dd104 : bv 32 := 0x0da53823.

(* [comment removed for export] *)
Definition W_dd108 : bv 32 := 0x0db53c23.

(* [comment removed for export] *)
Definition W_dd10c : bv 32 := 0x0fc53023.

(* [comment removed for export] *)
Definition W_dd110 : bv 32 := 0x0fd53423.

(* [comment removed for export] *)
Definition W_dd114 : bv 32 := 0x0fe53823.

(* [comment removed for export] *)
Definition W_dd118 : bv 32 := 0x0ff53c23.

(* [comment removed for export] *)
Definition W_dd11c : bv 32 := 0x10053027.

(* [comment removed for export] *)
Definition W_dd120 : bv 32 := 0x10153427.

(* [comment removed for export] *)
Definition W_dd124 : bv 32 := 0x10253827.

(* [comment removed for export] *)
Definition W_dd128 : bv 32 := 0x10353c27.

(* [comment removed for export] *)
Definition W_dd12c : bv 32 := 0x12453027.

(* [comment removed for export] *)
Definition W_dd130 : bv 32 := 0x12553427.

(* [comment removed for export] *)
Definition W_dd134 : bv 32 := 0x12653827.

(* [comment removed for export] *)
Definition W_dd138 : bv 32 := 0x12753c27.

(* [comment removed for export] *)
Definition W_dd13c : bv 32 := 0x14853027.

(* [comment removed for export] *)
Definition W_dd140 : bv 32 := 0x14953427.

(* [comment removed for export] *)
Definition W_dd144 : bv 32 := 0x14a53827.

(* [comment removed for export] *)
Definition W_dd148 : bv 32 := 0x14b53c27.

(* [comment removed for export] *)
Definition W_dd14c : bv 32 := 0x16c53027.

(* [comment removed for export] *)
Definition W_dd150 : bv 32 := 0x16d53427.

(* [comment removed for export] *)
Definition W_dd154 : bv 32 := 0x16e53827.

(* [comment removed for export] *)
Definition W_dd158 : bv 32 := 0x16f53c27.

(* [comment removed for export] *)
Definition W_dd15c : bv 32 := 0x19053027.

(* [comment removed for export] *)
Definition W_dd160 : bv 32 := 0x19153427.

(* [comment removed for export] *)
Definition W_dd164 : bv 32 := 0x19253827.

(* [comment removed for export] *)
Definition W_dd168 : bv 32 := 0x19353c27.

(* [comment removed for export] *)
Definition W_dd16c : bv 32 := 0x1b453027.

(* [comment removed for export] *)
Definition W_dd170 : bv 32 := 0x1b553427.

(* [comment removed for export] *)
Definition W_dd174 : bv 32 := 0x1b653827.

(* [comment removed for export] *)
Definition W_dd178 : bv 32 := 0x1b753c27.

(* [comment removed for export] *)
Definition W_dd17c : bv 32 := 0x1d853027.

(* [comment removed for export] *)
Definition W_dd180 : bv 32 := 0x1d953427.

(* [comment removed for export] *)
Definition W_dd184 : bv 32 := 0x1da53827.

(* [comment removed for export] *)
Definition W_dd188 : bv 32 := 0x1db53c27.

(* [comment removed for export] *)
Definition W_dd18c : bv 32 := 0x1fc53027.

(* [comment removed for export] *)
Definition W_dd190 : bv 32 := 0x1fd53427.

(* [comment removed for export] *)
Definition W_dd194 : bv 32 := 0x1fe53827.

(* [comment removed for export] *)
Definition W_dd198 : bv 32 := 0x1ff53c27.

(* [comment removed for export] *)
Definition W_dd19c : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_dd1a0 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd1a4 : bv 32 := 0xde010113.

(* [comment removed for export] *)
Definition W_dd1a8 : bv 32 := 0x20113c23.

(* [comment removed for export] *)
Definition W_dd1ac : bv 32 := 0x20813823.

(* [comment removed for export] *)
Definition W_dd1b0 : bv 32 := 0x20913423.

(* [comment removed for export] *)
Definition W_dd1b4 : bv 32 := 0x00050413.

(* [comment removed for export] *)
Definition W_dd1b8 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dd1bc : bv 32 := 0x56c53483.

(* [comment removed for export] *)
Definition W_dd1c0 : bv 32 := 0x0004b503.

(* [comment removed for export] *)
Definition W_dd1c4 : bv 32 := 0x0fa00593.

(* [comment removed for export] *)
Definition W_dd1c8 : bv 32 := 0x20a13023.

(* [comment removed for export] *)
Definition W_dd1cc : bv 32 := 0x0685e663.

(* [comment removed for export] *)
Definition W_dd1d0 : bv 32 := 0x00141513.

(* [comment removed for export] *)
Definition W_dd1d4 : bv 32 := 0xfff52597.

(* [comment removed for export] *)
Definition W_dd1d8 : bv 32 := 0x5dc58593.

(* [comment removed for export] *)
Definition W_dd1dc : bv 32 := 0x00a58533.

(* [comment removed for export] *)
Definition W_dd1e0 : bv 32 := 0x00051503.

(* [comment removed for export] *)
Definition W_dd1e4 : bv 32 := 0x04050a63.

(* [comment removed for export] *)
Definition W_dd1e8 : bv 32 := 0xfff00593.

(* [comment removed for export] *)
Definition W_dd1ec : bv 32 := 0x04b55e63.

(* [comment removed for export] *)
Definition W_dd1f0 : bv 32 := 0x0ff47593.

(* [comment removed for export] *)
Definition W_dd1f4 : bv 32 := 0x00400613.

(* [comment removed for export] *)
Definition W_dd1f8 : bv 32 := 0x00c58663.

(* [comment removed for export] *)
Definition W_dd1fc : bv 32 := 0x00100613.

(* [comment removed for export] *)
Definition W_dd200 : bv 32 := 0x06c59463.

(* [comment removed for export] *)
Definition W_dd204 : bv 32 := 0x03251513.

(* [comment removed for export] *)
Definition W_dd208 : bv 32 := 0x03255513.

(* [comment removed for export] *)
Definition W_dd20c : bv 32 := 0x00010593.

(* [comment removed for export] *)
Definition W_dd210 : bv 32 := 0x52d040ef.

(* [comment removed for export] *)
Definition W_dd214 : bv 32 := 0x00013503.

(* [comment removed for export] *)
Definition W_dd218 : bv 32 := 0xfff00613.

(* [comment removed for export] *)
Definition W_dd21c : bv 32 := 0x00165613.

(* [comment removed for export] *)
Definition W_dd220 : bv 32 := 0xfff53593.

(* [comment removed for export] *)
Definition W_dd224 : bv 32 := 0x00c56463.

(* [comment removed for export] *)
Definition W_dd228 : bv 32 := 0x00060513.

(* [comment removed for export] *)
Definition W_dd22c : bv 32 := 0xfff58593.

(* [comment removed for export] *)
Definition W_dd230 : bv 32 := 0x00a5e533.

(* [comment removed for export] *)
Definition W_dd234 : bv 32 := 0x0140006f.

(* [comment removed for export] *)
Definition W_dd238 : bv 32 := 0x0a9000ef.

(* [comment removed for export] *)
Definition W_dd23c : bv 32 := 0x01600593.

(* [comment removed for export] *)
Definition W_dd240 : bv 32 := 0x00b52023.

(* [comment removed for export] *)
Definition W_dd244 : bv 32 := 0xfff00513.

(* [comment removed for export] *)
Definition W_dd248 : bv 32 := 0x0004b583.

(* [comment removed for export] *)
Definition W_dd24c : bv 32 := 0x20013603.

(* [comment removed for export] *)
Definition W_dd250 : bv 32 := 0x16c59c63.

(* [comment removed for export] *)
Definition W_dd254 : bv 32 := 0x21813083.

(* [comment removed for export] *)
Definition W_dd258 : bv 32 := 0x21013403.

(* [comment removed for export] *)
Definition W_dd25c : bv 32 := 0x20813483.

(* [comment removed for export] *)
Definition W_dd260 : bv 32 := 0x22010113.

(* [comment removed for export] *)
Definition W_dd264 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd268 : bv 32 := 0x0ff57593.

(* [comment removed for export] *)
Definition W_dd26c : bv 32 := 0xfff58593.

(* [comment removed for export] *)
Definition W_dd270 : bv 32 := 0x00c00613.

(* [comment removed for export] *)
Definition W_dd274 : bv 32 := 0xfcb66ae3.

(* [comment removed for export] *)
Definition W_dd278 : bv 32 := 0x00259593.

(* [comment removed for export] *)
Definition W_dd27c : bv 32 := 0xfff52517.

(* [comment removed for export] *)
Definition W_dd280 : bv 32 := 0x50050513.

(* [comment removed for export] *)
Definition W_dd284 : bv 32 := 0x00a585b3.

(* [comment removed for export] *)
Definition W_dd288 : bv 32 := 0x0005a583.

(* [comment removed for export] *)
Definition W_dd28c : bv 32 := 0x00031637.

(* [comment removed for export] *)
Definition W_dd290 : bv 32 := 0x00a585b3.

(* [comment removed for export] *)
Definition W_dd294 : bv 32 := 0x0696051b.

(* [comment removed for export] *)
Definition W_dd298 : bv 32 := 0x00058067.

(* [comment removed for export] *)
Definition W_dd29c : bv 32 := 0x80000537.

(* [comment removed for export] *)
Definition W_dd2a0 : bv 32 := 0xfff5051b.

(* [comment removed for export] *)
Definition W_dd2a4 : bv 32 := 0xfa5ff06f.

(* [comment removed for export] *)
Definition W_dd2a8 : bv 32 := 0x03300513.

(* [comment removed for export] *)
Definition W_dd2ac : bv 32 := 0x429040ef.

(* [comment removed for export] *)
Definition W_dd2b0 : bv 32 := 0x40000593.

(* [comment removed for export] *)
Definition W_dd2b4 : bv 32 := 0x00a5e463.

(* [comment removed for export] *)
Definition W_dd2b8 : bv 32 := 0x40000513.

(* [comment removed for export] *)
Definition W_dd2bc : bv 32 := 0x0fa00613.

(* [comment removed for export] *)
Definition W_dd2c0 : bv 32 := 0x00c41663.

(* [comment removed for export] *)
Definition W_dd2c4 : bv 32 := 0x00700593.

(* [comment removed for export] *)
Definition W_dd2c8 : bv 32 := 0x00a59593.

(* [comment removed for export] *)
Definition W_dd2cc : bv 32 := 0x00b50533.

(* [comment removed for export] *)
Definition W_dd2d0 : bv 32 := 0x02051513.

(* [comment removed for export] *)
Definition W_dd2d4 : bv 32 := 0x02055513.

(* [comment removed for export] *)
Definition W_dd2d8 : bv 32 := 0xf71ff06f.

(* [comment removed for export] *)
Definition W_dd2dc : bv 32 := 0x01010513.

(* [comment removed for export] *)
Definition W_dd2e0 : bv 32 := 0x238010ef.

(* [comment removed for export] *)
Definition W_dd2e4 : bv 32 := 0x07812503.

(* [comment removed for export] *)
Definition W_dd2e8 : bv 32 := 0x00153593.

(* [comment removed for export] *)
Definition W_dd2ec : bv 32 := 0x05500613.

(* [comment removed for export] *)
Definition W_dd2f0 : bv 32 := 0x00b50533.

(* [comment removed for export] *)
Definition W_dd2f4 : bv 32 := 0x08c40063.

(* [comment removed for export] *)
Definition W_dd2f8 : bv 32 := 0x03813583.

(* [comment removed for export] *)
Definition W_dd2fc : bv 32 := 0x04813603.

(* [comment removed for export] *)
Definition W_dd300 : bv 32 := 0x00b605b3.

(* [comment removed for export] *)
Definition W_dd304 : bv 32 := 0x0740006f.

(* [comment removed for export] *)
Definition W_dd308 : bv 32 := 0x18110513.

(* [comment removed for export] *)
Definition W_dd30c : bv 32 := 0x07f00613.

(* [comment removed for export] *)
Definition W_dd310 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_dd314 : bv 32 := 0xee4870ef.

(* [comment removed for export] *)
Definition W_dd318 : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_dd31c : bv 32 := 0x00000693.

(* [comment removed for export] *)
Definition W_dd320 : bv 32 := 0x00100613.

(* [comment removed for export] *)
Definition W_dd324 : bv 32 := 0x07b00893.

(* [comment removed for export] *)
Definition W_dd328 : bv 32 := 0x08000593.

(* [comment removed for export] *)
Definition W_dd32c : bv 32 := 0x18c10023.

(* [comment removed for export] *)
Definition W_dd330 : bv 32 := 0x18010613.

(* [comment removed for export] *)
Definition W_dd334 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dd338 : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_dd33c : bv 32 := 0x08000593.

(* [comment removed for export] *)
Definition W_dd340 : bv 32 := 0x00c0006f.

(* [comment removed for export] *)
Definition W_dd344 : bv 32 := 0x00168693.

(* [comment removed for export] *)
Definition W_dd348 : bv 32 := 0xf0b680e3.

(* [comment removed for export] *)
Definition W_dd34c : bv 32 := 0x00d60733.

(* [comment removed for export] *)
Definition W_dd350 : bv 32 := 0x00074783.

(* [comment removed for export] *)
Definition W_dd354 : bv 32 := 0xfe0788e3.

(* [comment removed for export] *)
Definition W_dd358 : bv 32 := 0xfff78813.

(* [comment removed for export] *)
Definition W_dd35c : bv 32 := 0x00f877b3.

(* [comment removed for export] *)
Definition W_dd360 : bv 32 := 0x0ff7f813.

(* [comment removed for export] *)
Definition W_dd364 : bv 32 := 0x0015051b.

(* [comment removed for export] *)
Definition W_dd368 : bv 32 := 0xfe0818e3.

(* [comment removed for export] *)
Definition W_dd36c : bv 32 := 0x00070023.

(* [comment removed for export] *)
Definition W_dd370 : bv 32 := 0xfd5ff06f.

(* [comment removed for export] *)
Definition W_dd374 : bv 32 := 0x03013583.

(* [comment removed for export] *)
Definition W_dd378 : bv 32 := 0x0057c617.

(* [comment removed for export] *)
Definition W_dd37c : bv 32 := 0x61c63603.

(* [comment removed for export] *)
Definition W_dd380 : bv 32 := 0x02051513.

(* [comment removed for export] *)
Definition W_dd384 : bv 32 := 0x02055513.

(* [comment removed for export] *)
Definition W_dd388 : bv 32 := 0x02a58533.

(* [comment removed for export] *)
Definition W_dd38c : bv 32 := 0x02c55533.

(* [comment removed for export] *)
Definition W_dd390 : bv 32 := 0xfff00593.

(* [comment removed for export] *)
Definition W_dd394 : bv 32 := 0x0015d593.

(* [comment removed for export] *)
Definition W_dd398 : bv 32 := 0xeab568e3.

(* [comment removed for export] *)
Definition W_dd39c : bv 32 := 0x00058513.

(* [comment removed for export] *)
Definition W_dd3a0 : bv 32 := 0xea9ff06f.

(* [comment removed for export] *)
Definition W_dd3a4 : bv 32 := 0x00008537.

(* [comment removed for export] *)
Definition W_dd3a8 : bv 32 := 0xea1ff06f.

(* [comment removed for export] *)
Definition W_dd3ac : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_dd3b0 : bv 32 := 0x5e853503.

(* [comment removed for export] *)
Definition W_dd3b4 : bv 32 := 0xe95ff06f.

(* [comment removed for export] *)
Definition W_dd3b8 : bv 32 := 0x00020537.

(* [comment removed for export] *)
Definition W_dd3bc : bv 32 := 0xe8dff06f.

(* [comment removed for export] *)
Definition W_dd3c0 : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_dd3c4 : bv 32 := 0xe85ff06f.

(* [comment removed for export] *)
Definition W_dd3c8 : bv 32 := 0x710000ef.

(* [comment removed for export] *)
Definition W_dd3cc : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd3d0 : bv 32 := 0xe8010113.

(* [comment removed for export] *)
Definition W_dd3d4 : bv 32 := 0x16113c23.

(* [comment removed for export] *)
Definition W_dd3d8 : bv 32 := 0x16813823.

(* [comment removed for export] *)
Definition W_dd3dc : bv 32 := 0x16913423.

(* [comment removed for export] *)
Definition W_dd3e0 : bv 32 := 0x17213023.

(* [comment removed for export] *)
Definition W_dd3e4 : bv 32 := 0x00058413.

(* [comment removed for export] *)
Definition W_dd3e8 : bv 32 := 0x00050493.

(* [comment removed for export] *)
Definition W_dd3ec : bv 32 := 0x03010513.

(* [comment removed for export] *)
Definition W_dd3f0 : bv 32 := 0x13000613.

(* [comment removed for export] *)
Definition W_dd3f4 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_dd3f8 : bv 32 := 0xe00870ef.

(* [comment removed for export] *)
Definition W_dd3fc : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dd400 : bv 32 := 0x33053503.

(* [comment removed for export] *)
Definition W_dd404 : bv 32 := 0x00953023.

(* [comment removed for export] *)
Definition W_dd408 : bv 32 := 0x0004b503.

(* [comment removed for export] *)
Definition W_dd40c : bv 32 := 0x00848493.

(* [comment removed for export] *)
Definition W_dd410 : bv 32 := 0xfe051ce3.

(* [comment removed for export] *)
Definition W_dd414 : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_dd418 : bv 32 := 0x55050913.

(* [comment removed for export] *)
Definition W_dd41c : bv 32 := 0x00993423.

(* [comment removed for export] *)
Definition W_dd420 : bv 32 := 0x0004b583.

(* [comment removed for export] *)
Definition W_dd424 : bv 32 := 0x04058c63.

(* [comment removed for export] *)
Definition W_dd428 : bv 32 := 0x01048493.

(* [comment removed for export] *)
Definition W_dd42c : bv 32 := 0x02500513.

(* [comment removed for export] *)
Definition W_dd430 : bv 32 := 0x03010613.

(* [comment removed for export] *)
Definition W_dd434 : bv 32 := 0x0100006f.

(* [comment removed for export] *)
Definition W_dd438 : bv 32 := 0x0004b583.

(* [comment removed for export] *)
Definition W_dd43c : bv 32 := 0x01048493.

(* [comment removed for export] *)
Definition W_dd440 : bv 32 := 0x00058e63.

(* [comment removed for export] *)
Definition W_dd444 : bv 32 := 0xfeb56ae3.

(* [comment removed for export] *)
Definition W_dd448 : bv 32 := 0xff84b683.

(* [comment removed for export] *)
Definition W_dd44c : bv 32 := 0x00359593.

(* [comment removed for export] *)
Definition W_dd450 : bv 32 := 0x00b605b3.

(* [comment removed for export] *)
Definition W_dd454 : bv 32 := 0x00d5b023.

(* [comment removed for export] *)
Definition W_dd458 : bv 32 := 0xfe1ff06f.

(* [comment removed for export] *)
Definition W_dd45c : bv 32 := 0x0b013583.

(* [comment removed for export] *)
Definition W_dd460 : bv 32 := 0x13013503.

(* [comment removed for export] *)
Definition W_dd464 : bv 32 := 0x0057c617.

(* [comment removed for export] *)
Definition W_dd468 : bv 32 := 0x56b63423.

(* [comment removed for export] *)
Definition W_dd46c : bv 32 := 0x00050c63.

(* [comment removed for export] *)
Definition W_dd470 : bv 32 := 0x0057c597.

(* [comment removed for export] *)
Definition W_dd474 : bv 32 := 0x4ca5be23.

(* [comment removed for export] *)
Definition W_dd478 : bv 32 := 0x00c0006f.

(* [comment removed for export] *)
Definition W_dd47c : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_dd480 : bv 32 := 0x54053823.

(* [comment removed for export] *)
Definition W_dd484 : bv 32 := 0x06013503.

(* [comment removed for export] *)
Definition W_dd488 : bv 32 := 0x02a93823.

(* [comment removed for export] *)
Definition W_dd48c : bv 32 := 0x00041463.

(* [comment removed for export] *)
Definition W_dd490 : bv 32 := 0x12813403.

(* [comment removed for export] *)
Definition W_dd494 : bv 32 := 0x00041663.

(* [comment removed for export] *)
Definition W_dd498 : bv 32 := 0xfff34517.

(* [comment removed for export] *)
Definition W_dd49c : bv 32 := 0x5a250413.

(* [comment removed for export] *)
Definition W_dd4a0 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dd4a4 : bv 32 := 0x29453583.

(* [comment removed for export] *)
Definition W_dd4a8 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dd4ac : bv 32 := 0x29453503.

(* [comment removed for export] *)
Definition W_dd4b0 : bv 32 := 0x0085b023.

(* [comment removed for export] *)
Definition W_dd4b4 : bv 32 := 0x00140593.

(* [comment removed for export] *)
Definition W_dd4b8 : bv 32 := 0x00853023.

(* [comment removed for export] *)
Definition W_dd4bc : bv 32 := 0x02f00613.

(* [comment removed for export] *)
Definition W_dd4c0 : bv 32 := 0x00c0006f.

(* [comment removed for export] *)
Definition W_dd4c4 : bv 32 := 0x00b53023.

(* [comment removed for export] *)
Definition W_dd4c8 : bv 32 := 0x00158593.

(* [comment removed for export] *)
Definition W_dd4cc : bv 32 := 0xfff5c683.

(* [comment removed for export] *)
Definition W_dd4d0 : bv 32 := 0xfec68ae3.

(* [comment removed for export] *)
Definition W_dd4d4 : bv 32 := 0xfe069ae3.

(* [comment removed for export] *)
Definition W_dd4d8 : bv 32 := 0x03010513.

(* [comment removed for export] *)
Definition W_dd4dc : bv 32 := 0x2ec000ef.

(* [comment removed for export] *)
Definition W_dd4e0 : bv 32 := 0x0f813503.

(* [comment removed for export] *)
Definition W_dd4e4 : bv 32 := 0x594000ef.

(* [comment removed for export] *)
Definition W_dd4e8 : bv 32 := 0x08813503.

(* [comment removed for export] *)
Definition W_dd4ec : bv 32 := 0x09013583.

(* [comment removed for export] *)
Definition W_dd4f0 : bv 32 := 0x00b51c63.

(* [comment removed for export] *)
Definition W_dd4f4 : bv 32 := 0x09813503.

(* [comment removed for export] *)
Definition W_dd4f8 : bv 32 := 0x0a013583.

(* [comment removed for export] *)
Definition W_dd4fc : bv 32 := 0x00b51663.

(* [comment removed for export] *)
Definition W_dd500 : bv 32 := 0x0e813503.

(* [comment removed for export] *)
Definition W_dd504 : bv 32 := 0x0e050063.

(* [comment removed for export] *)
Definition W_dd508 : bv 32 := 0x00200693.

(* [comment removed for export] *)
Definition W_dd50c : bv 32 := 0x00100793.

(* [comment removed for export] *)
Definition W_dd510 : bv 32 := 0x00013423.

(* [comment removed for export] *)
Definition W_dd514 : bv 32 := 0x00013823.

(* [comment removed for export] *)
Definition W_dd518 : bv 32 := 0x04900893.

(* [comment removed for export] *)
Definition W_dd51c : bv 32 := 0x01810513.

(* [comment removed for export] *)
Definition W_dd520 : bv 32 := 0x00300593.

(* [comment removed for export] *)
Definition W_dd524 : bv 32 := 0x00810613.

(* [comment removed for export] *)
Definition W_dd528 : bv 32 := 0x00800713.

(* [comment removed for export] *)
Definition W_dd52c : bv 32 := 0x00013c23.

(* [comment removed for export] *)
Definition W_dd530 : bv 32 := 0x02f13023.

(* [comment removed for export] *)
Definition W_dd534 : bv 32 := 0x02d13423.

(* [comment removed for export] *)
Definition W_dd538 : bv 32 := 0x00000693.

(* [comment removed for export] *)
Definition W_dd53c : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dd540 : bv 32 := 0x02051513.

(* [comment removed for export] *)
Definition W_dd544 : bv 32 := 0x00055463.

(* [comment removed for export] *)
Definition W_dd548 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dd54c : bv 32 := 0x01e15503.

(* [comment removed for export] *)
Definition W_dd550 : bv 32 := 0x02057513.

(* [comment removed for export] *)
Definition W_dd554 : bv 32 := 0x02050463.

(* [comment removed for export] *)
Definition W_dd558 : bv 32 := 0xfff44517.

(* [comment removed for export] *)
Definition W_dd55c : bv 32 := 0x00008637.

(* [comment removed for export] *)
Definition W_dd560 : bv 32 := 0x03800893.

(* [comment removed for export] *)
Definition W_dd564 : bv 32 := 0xc3950593.

(* [comment removed for export] *)
Definition W_dd568 : bv 32 := 0x0026061b.

(* [comment removed for export] *)
Definition W_dd56c : bv 32 := 0xf9c00513.

(* [comment removed for export] *)
Definition W_dd570 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dd574 : bv 32 := 0x00055463.

(* [comment removed for export] *)
Definition W_dd578 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dd57c : bv 32 := 0x02615503.

(* [comment removed for export] *)
Definition W_dd580 : bv 32 := 0x02057513.

(* [comment removed for export] *)
Definition W_dd584 : bv 32 := 0x02050463.

(* [comment removed for export] *)
Definition W_dd588 : bv 32 := 0xfff44517.

(* [comment removed for export] *)
Definition W_dd58c : bv 32 := 0x00008637.

(* [comment removed for export] *)
Definition W_dd590 : bv 32 := 0x03800893.

(* [comment removed for export] *)
Definition W_dd594 : bv 32 := 0xc0950593.

(* [comment removed for export] *)
Definition W_dd598 : bv 32 := 0x0026061b.

(* [comment removed for export] *)
Definition W_dd59c : bv 32 := 0xf9c00513.

(* [comment removed for export] *)
Definition W_dd5a0 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dd5a4 : bv 32 := 0x00055463.

(* [comment removed for export] *)
Definition W_dd5a8 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dd5ac : bv 32 := 0x02e15503.

(* [comment removed for export] *)
Definition W_dd5b0 : bv 32 := 0x02057513.

(* [comment removed for export] *)
Definition W_dd5b4 : bv 32 := 0x02050463.

(* [comment removed for export] *)
Definition W_dd5b8 : bv 32 := 0xfff44517.

(* [comment removed for export] *)
Definition W_dd5bc : bv 32 := 0x00008637.

(* [comment removed for export] *)
Definition W_dd5c0 : bv 32 := 0x03800893.

(* [comment removed for export] *)
Definition W_dd5c4 : bv 32 := 0xbd950593.

(* [comment removed for export] *)
Definition W_dd5c8 : bv 32 := 0x0026061b.

(* [comment removed for export] *)
Definition W_dd5cc : bv 32 := 0xf9c00513.

(* [comment removed for export] *)
Definition W_dd5d0 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dd5d4 : bv 32 := 0x00055463.

(* [comment removed for export] *)
Definition W_dd5d8 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dd5dc : bv 32 := 0x00100513.

(* [comment removed for export] *)
Definition W_dd5e0 : bv 32 := 0x00a90123.

(* [comment removed for export] *)
Definition W_dd5e4 : bv 32 := 0x17813083.

(* [comment removed for export] *)
Definition W_dd5e8 : bv 32 := 0x17013403.

(* [comment removed for export] *)
Definition W_dd5ec : bv 32 := 0x16813483.

(* [comment removed for export] *)
Definition W_dd5f0 : bv 32 := 0x16013903.

(* [comment removed for export] *)
Definition W_dd5f4 : bv 32 := 0x18010113.

(* [comment removed for export] *)
Definition W_dd5f8 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd5fc : bv 32 := 0xfe010113.

(* [comment removed for export] *)
Definition W_dd600 : bv 32 := 0x00113c23.

(* [comment removed for export] *)
Definition W_dd604 : bv 32 := 0x00813823.

(* [comment removed for export] *)
Definition W_dd608 : bv 32 := 0x00913423.

(* [comment removed for export] *)
Definition W_dd60c : bv 32 := 0xdc1ff0ef.

(* [comment removed for export] *)
Definition W_dd610 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dd614 : bv 32 := 0x00016597.

(* [comment removed for export] *)
Definition W_dd618 : bv 32 := 0x13453403.

(* [comment removed for export] *)
Definition W_dd61c : bv 32 := 0x1385b483.

(* [comment removed for export] *)
Definition W_dd620 : bv 32 := 0x0084fa63.

(* [comment removed for export] *)
Definition W_dd624 : bv 32 := 0x0004b503.

(* [comment removed for export] *)
Definition W_dd628 : bv 32 := 0x000500e7.

(* [comment removed for export] *)
Definition W_dd62c : bv 32 := 0x00848493.

(* [comment removed for export] *)
Definition W_dd630 : bv 32 := 0xfe84eae3.

(* [comment removed for export] *)
Definition W_dd634 : bv 32 := 0x01813083.

(* [comment removed for export] *)
Definition W_dd638 : bv 32 := 0x01013403.

(* [comment removed for export] *)
Definition W_dd63c : bv 32 := 0x00813483.

(* [comment removed for export] *)
Definition W_dd640 : bv 32 := 0x02010113.

(* [comment removed for export] *)
Definition W_dd644 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd648 : bv 32 := 0xfe010113.

(* [comment removed for export] *)
Definition W_dd64c : bv 32 := 0x00113c23.

(* [comment removed for export] *)
Definition W_dd650 : bv 32 := 0x00813823.

(* [comment removed for export] *)
Definition W_dd654 : bv 32 := 0x00913423.

(* [comment removed for export] *)
Definition W_dd658 : bv 32 := 0x01213023.

(* [comment removed for export] *)
Definition W_dd65c : bv 32 := 0x00060413.

(* [comment removed for export] *)
Definition W_dd660 : bv 32 := 0x00058493.

(* [comment removed for export] *)
Definition W_dd664 : bv 32 := 0x00050913.

(* [comment removed for export] *)
Definition W_dd668 : bv 32 := 0x00063583.

(* [comment removed for export] *)
Definition W_dd66c : bv 32 := 0x00349513.

(* [comment removed for export] *)
Definition W_dd670 : bv 32 := 0x00a60533.

(* [comment removed for export] *)
Definition W_dd674 : bv 32 := 0x00850513.

(* [comment removed for export] *)
Definition W_dd678 : bv 32 := 0xd59ff0ef.

(* [comment removed for export] *)
Definition W_dd67c : bv 32 := 0x00000517.

(* [comment removed for export] *)
Definition W_dd680 : bv 32 := 0x02c50313.

(* [comment removed for export] *)
Definition W_dd684 : bv 32 := 0x00090513.

(* [comment removed for export] *)
Definition W_dd688 : bv 32 := 0x00048593.

(* [comment removed for export] *)
Definition W_dd68c : bv 32 := 0x00040613.

(* [comment removed for export] *)
Definition W_dd690 : bv 32 := 0x01813083.

(* [comment removed for export] *)
Definition W_dd694 : bv 32 := 0x01013403.

(* [comment removed for export] *)
Definition W_dd698 : bv 32 := 0x00813483.

(* [comment removed for export] *)
Definition W_dd69c : bv 32 := 0x00013903.

(* [comment removed for export] *)
Definition W_dd6a0 : bv 32 := 0x02010113.

(* [comment removed for export] *)
Definition W_dd6a4 : bv 32 := 0x00030067.

(* [comment removed for export] *)
Definition W_dd6a8 : bv 32 := 0xfd010113.

(* [comment removed for export] *)
Definition W_dd6ac : bv 32 := 0x02113423.

(* [comment removed for export] *)
Definition W_dd6b0 : bv 32 := 0x02813023.

(* [comment removed for export] *)
Definition W_dd6b4 : bv 32 := 0x00913c23.

(* [comment removed for export] *)
Definition W_dd6b8 : bv 32 := 0x01213823.

(* [comment removed for export] *)
Definition W_dd6bc : bv 32 := 0x01313423.

(* [comment removed for export] *)
Definition W_dd6c0 : bv 32 := 0x00060413.

(* [comment removed for export] *)
Definition W_dd6c4 : bv 32 := 0x00058493.

(* [comment removed for export] *)
Definition W_dd6c8 : bv 32 := 0x00050913.

(* [comment removed for export] *)
Definition W_dd6cc : bv 32 := 0x00359513.

(* [comment removed for export] *)
Definition W_dd6d0 : bv 32 := 0x00a60533.

(* [comment removed for export] *)
Definition W_dd6d4 : bv 32 := 0x00850993.

(* [comment removed for export] *)
Definition W_dd6d8 : bv 32 := 0xf25ff0ef.

(* [comment removed for export] *)
Definition W_dd6dc : bv 32 := 0x00048513.

(* [comment removed for export] *)
Definition W_dd6e0 : bv 32 := 0x00040593.

(* [comment removed for export] *)
Definition W_dd6e4 : bv 32 := 0x00098613.

(* [comment removed for export] *)
Definition W_dd6e8 : bv 32 := 0x000900e7.

(* [comment removed for export] *)
Definition W_dd6ec : bv 32 := 0x700000ef.
Lemma F_dd6ec : fetch_word AsanUbsan.M.loaded_segments (0xe0aa8 : word) = Some W_dd6ec.
Proof. vm_refl. Qed.
Lemma D_dd6ec : decode_any W_dd6ec = Some (Jal 1 1792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dd6f0 : bv 32 := 0xfc010113.

(* [comment removed for export] *)
Definition W_dd6f4 : bv 32 := 0x02113c23.

(* [comment removed for export] *)
Definition W_dd6f8 : bv 32 := 0x02813823.

(* [comment removed for export] *)
Definition W_dd6fc : bv 32 := 0x02913423.

(* [comment removed for export] *)
Definition W_dd700 : bv 32 := 0x03213023.

(* [comment removed for export] *)
Definition W_dd704 : bv 32 := 0x01313c23.

(* [comment removed for export] *)
Definition W_dd708 : bv 32 := 0x01413823.

(* [comment removed for export] *)
Definition W_dd70c : bv 32 := 0x01513423.

(* [comment removed for export] *)
Definition W_dd710 : bv 32 := 0x0057c597.

(* [comment removed for export] *)
Definition W_dd714 : bv 32 := 0xf3800693.

(* [comment removed for export] *)
Definition W_dd718 : bv 32 := 0x25458493.

(* [comment removed for export] *)
Definition W_dd71c : bv 32 := 0x0104b903.

(* [comment removed for export] *)
Definition W_dd720 : bv 32 := 0x0184b603.

(* [comment removed for export] *)
Definition W_dd724 : bv 32 := 0x0204b703.

(* [comment removed for export] *)
Definition W_dd728 : bv 32 := 0x40a686b3.

(* [comment removed for export] *)
Definition W_dd72c : bv 32 := 0x0284b583.

(* [comment removed for export] *)
Definition W_dd730 : bv 32 := 0x00c509b3.

(* [comment removed for export] *)
Definition W_dd734 : bv 32 := 0xfff70713.

(* [comment removed for export] *)
Definition W_dd738 : bv 32 := 0x00d776b3.

(* [comment removed for export] *)
Definition W_dd73c : bv 32 := 0xfff5c713.

(* [comment removed for export] *)
Definition W_dd740 : bv 32 := 0x00371713.

(* [comment removed for export] *)
Definition W_dd744 : bv 32 := 0x00e989b3.

(* [comment removed for export] *)
Definition W_dd748 : bv 32 := 0x00d50433.

(* [comment removed for export] *)
Definition W_dd74c : bv 32 := 0x04090663.

(* [comment removed for export] *)
Definition W_dd750 : bv 32 := 0x0c840a13.

(* [comment removed for export] *)
Definition W_dd754 : bv 32 := 0x00359593.

(* [comment removed for export] *)
Definition W_dd758 : bv 32 := 0x00c50533.

(* [comment removed for export] *)
Definition W_dd75c : bv 32 := 0x40b50ab3.

(* [comment removed for export] *)
Definition W_dd760 : bv 32 := 0x02893503.

(* [comment removed for export] *)
Definition W_dd764 : bv 32 := 0x00aa0533.

(* [comment removed for export] *)
Definition W_dd768 : bv 32 := 0x7ff50513.

(* [comment removed for export] *)
Definition W_dd76c : bv 32 := 0x00150513.

(* [comment removed for export] *)
Definition W_dd770 : bv 32 := 0x00aab023.

(* [comment removed for export] *)
Definition W_dd774 : bv 32 := 0x02893503.

(* [comment removed for export] *)
Definition W_dd778 : bv 32 := 0x00893583.

(* [comment removed for export] *)
Definition W_dd77c : bv 32 := 0x01093603.

(* [comment removed for export] *)
Definition W_dd780 : bv 32 := 0x00aa0533.

(* [comment removed for export] *)
Definition W_dd784 : bv 32 := 0xa78870ef.

(* [comment removed for export] *)
Definition W_dd788 : bv 32 := 0x00093903.

(* [comment removed for export] *)
Definition W_dd78c : bv 32 := 0x008a8a93.

(* [comment removed for export] *)
Definition W_dd790 : bv 32 := 0xfc0918e3.

(* [comment removed for export] *)
Definition W_dd794 : bv 32 := 0x0284b583.

(* [comment removed for export] *)
Definition W_dd798 : bv 32 := 0x00b9b023.

(* [comment removed for export] *)
Definition W_dd79c : bv 32 := 0x0d343023.

(* [comment removed for export] *)
Definition W_dd7a0 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_dd7a4 : bv 32 := 0x03813083.

(* [comment removed for export] *)
Definition W_dd7a8 : bv 32 := 0x03013403.

(* [comment removed for export] *)
Definition W_dd7ac : bv 32 := 0x02813483.

(* [comment removed for export] *)
Definition W_dd7b0 : bv 32 := 0x02013903.

(* [comment removed for export] *)
Definition W_dd7b4 : bv 32 := 0x01813983.

(* [comment removed for export] *)
Definition W_dd7b8 : bv 32 := 0x01013a03.

(* [comment removed for export] *)
Definition W_dd7bc : bv 32 := 0x00813a83.

(* [comment removed for export] *)
Definition W_dd7c0 : bv 32 := 0x04010113.

(* [comment removed for export] *)
Definition W_dd7c4 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dd7c8 : bv 32 := 0xfc010113.

(* [comment removed for export] *)
Definition W_dd7cc : bv 32 := 0x02113c23.

(* [comment removed for export] *)
Definition W_dd7d0 : bv 32 := 0x02813823.

(* [comment removed for export] *)
Definition W_dd7d4 : bv 32 := 0x02913423.

(* [comment removed for export] *)
Definition W_dd7d8 : bv 32 := 0x03213023.

(* [comment removed for export] *)
Definition W_dd7dc : bv 32 := 0x01313c23.

(* [comment removed for export] *)
Definition W_dd7e0 : bv 32 := 0x01413823.

(* [comment removed for export] *)
Definition W_dd7e4 : bv 32 := 0x01513423.

(* [comment removed for export] *)
Definition W_dd7e8 : bv 32 := 0x02853683.

(* [comment removed for export] *)
Definition W_dd7ec : bv 32 := 0x0057c597.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd7fc : bv 32 := 0x0c068e63.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd804 : bv 32 := 0x00000893.

(* [comment removed for export] *)
Definition W_dd808 : bv 32 := 0x0001a717.

(* [comment removed for export] *)
Definition W_dd80c : bv 32 := 0x01853783.

(* [comment removed for export] *)
Definition W_dd810 : bv 32 := 0x02053503.

(* [comment removed for export] *)
Definition W_dd814 : bv 32 := 0x00600813.

(* [comment removed for export] *)
Definition W_dd818 : bv 32 := 0x00015297.

(* [comment removed for export] *)
Definition W_dd81c : bv 32 := 0xb9476f03.

(* [comment removed for export] *)
Definition W_dd820 : bv 32 := 0x2242b283.

(* [comment removed for export] *)
Definition W_dd824 : bv 32 := 0x00200313.

(* [comment removed for export] *)
Definition W_dd828 : bv 32 := 0x00700393.

(* [comment removed for export] *)
Definition W_dd82c : bv 32 := 0x6474ee37.

(* [comment removed for export] *)
Definition W_dd830 : bv 32 := 0x551e0e1b.

(* [comment removed for export] *)
Definition W_dd834 : bv 32 := 0x00078e93.

(* [comment removed for export] *)
Definition W_dd838 : bv 32 := 0x0180006f.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd844 : bv 32 := 0xfff68693.

(* [comment removed for export] *)
Definition W_dd848 : bv 32 := 0x00ae8eb3.

(* [comment removed for export] *)
Definition W_dd84c : bv 32 := 0x04068a63.

(* [comment removed for export] *)
Definition W_dd850 : bv 32 := 0x000ea403.

(* [comment removed for export] *)
Definition W_dd854 : bv 32 := 0xff0404e3.

(* [comment removed for export] *)
Definition W_dd858 : bv 32 := 0x00028a63.

(* [comment removed for export] *)
Definition W_dd85c : bv 32 := 0x00641863.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd868 : bv 32 := 0xfddff06f.

(* [comment removed for export] *)
Definition W_dd86c : bv 32 := 0x000e8f93.

(* [comment removed for export] *)
Definition W_dd870 : bv 32 := 0x00740463.

(* [comment removed for export] *)
Definition W_dd874 : bv 32 := 0x00088f93.

(* [comment removed for export] *)
Definition W_dd878 : bv 32 := 0x03c41063.

(* [comment removed for export] *)
Definition W_dd87c : bv 32 := 0x028eb883.

(* [comment removed for export] *)
Definition W_dd880 : bv 32 := 0x011f7c63.

(* [comment removed for export] *)
Definition W_dd884 : bv 32 := 0x00800f37.

(* [comment removed for export] *)
Definition W_dd888 : bv 32 := 0x01e8e463.

(* [comment removed for export] *)
Definition W_dd88c : bv 32 := 0x008008b7.

(* [comment removed for export] *)
Definition W_dd890 : bv 32 := 0xb9172a23.

(* [comment removed for export] *)
Definition W_dd894 : bv 32 := 0x00088f13.

(* [comment removed for export] *)
Definition W_dd898 : bv 32 := 0x000f8893.

(* [comment removed for export] *)
Definition W_dd89c : bv 32 := 0xfa9ff06f.

(* [comment removed for export] *)
Definition W_dd8a0 : bv 32 := 0x02088c63.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd8a8 : bv 32 := 0x0108b783.

(* [comment removed for export] *)
Definition W_dd8ac : bv 32 := 0x0208b803.

(* [comment removed for export] *)
Definition W_dd8b0 : bv 32 := 0x0288b683.

(* [comment removed for export] *)
Definition W_dd8b4 : bv 32 := 0x0308b503.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd8bc : bv 32 := 0x00100793.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd8cc : bv 32 := 0x00e4b823.

(* [comment removed for export] *)
Definition W_dd8d0 : bv 32 := 0x02f4b423.

(* [comment removed for export] *)
Definition W_dd8d4 : bv 32 := 0x0100006f.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd8e8 : bv 32 := 0xfff50793.

(* [comment removed for export] *)
Definition W_dd8ec : bv 32 := 0x40e00733.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd8f4 : bv 32 := 0x00e7f733.

(* [comment removed for export] *)
Definition W_dd8f8 : bv 32 := 0x00700793.

(* [comment removed for export] *)
Definition W_dd8fc : bv 32 := 0x00d706b3.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd908 : bv 32 := 0x00a7e663.

(* [comment removed for export] *)
Definition W_dd90c : bv 32 := 0x00800513.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd924 : bv 32 := 0xff85f593.

(* [comment removed for export] *)
Definition W_dd928 : bv 32 := 0x00b4bc23.

(* [comment removed for export] *)
Definition W_dd92c : bv 32 := 0x02a4b023.

(* [comment removed for export] *)
Definition W_dd930 : bv 32 := 0x02d5ea63.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd960 : bv 32 := 0x05e00893.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd968 : bv 32 := 0x00000073.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd97c : bv 32 := 0x0284b603.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9a8 : bv 32 := 0x0c890413.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9b0 : bv 32 := 0x00361613.

(* [comment removed for export] *)
Definition W_dd9b4 : bv 32 := 0x40c50533.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9c0 : bv 32 := 0x00a40533.

(* [comment removed for export] *)
Definition W_dd9c4 : bv 32 := 0x7ff50513.

(* [comment removed for export] *)
Definition W_dd9c8 : bv 32 := 0x00150513.

(* [comment removed for export] *)
Definition W_dd9cc : bv 32 := 0x00aab023.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9dc : bv 32 := 0x00a40533.

(* [comment removed for export] *)
Definition W_dd9e0 : bv 32 := 0x828870ef.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9e8 : bv 32 := 0x008a8a93.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9f0 : bv 32 := 0x0284b603.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_dd9fc : bv 32 := 0x01293023.

(* [comment removed for export] *)
Definition W_dda00 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_dda04 : bv 32 := 0x2340c0ef.

(* [comment removed for export] *)
Definition W_dda08 : bv 32 := 0x04054a63.

(* [comment removed for export] *)
Definition W_dda0c : bv 32 := 0x00051663.

(* [comment removed for export] *)
Definition W_dda10 : bv 32 := 0x00100513.

(* [comment removed for export] *)
Definition W_dda14 : bv 32 := 0x00a48023.

(* [comment removed for export] *)
Definition W_dda18 : bv 32 := 0x00200513.

(* [comment removed for export] *)
Definition W_dda1c : bv 32 := 0x0057c597.

(* [comment removed for export] *)
Definition W_dda20 : bv 32 := 0x02a92423.

(* [comment removed for export] *)
Definition W_dda24 : bv 32 := 0x06000893.

(* [comment removed for export] *)
Definition W_dda28 : bv 32 := 0xccc58513.

(* [comment removed for export] *)
Definition W_dda2c : bv 32 := 0x03848593.

(* [comment removed for export] *)
Definition W_dda30 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dda34 : bv 32 := 0x07890613.

(* [comment removed for export] *)
Definition W_dda38 : bv 32 := 0x02a92023.

(* [comment removed for export] *)
Definition W_dda3c : bv 32 := 0x08b93c23.

(* [comment removed for export] *)
Definition W_dda40 : bv 32 := 0x06c93c23.

(* [comment removed for export] *)
Definition W_dda44 : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_dda48 : bv 32 := 0xf1453503.

(* [comment removed for export] *)
Definition W_dda4c : bv 32 := 0x01293423.

(* [comment removed for export] *)
Definition W_dda50 : bv 32 := 0x01293823.

(* [comment removed for export] *)
Definition W_dda54 : bv 32 := 0x00a93c23.

(* [comment removed for export] *)
Definition W_dda58 : bv 32 := 0x0080006f.

(* [comment removed for export] *)
Definition W_dda5c : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dda60 : bv 32 := 0x03813083.

(* [comment removed for export] *)
Definition W_dda64 : bv 32 := 0x03013403.

(* [comment removed for export] *)
Definition W_dda68 : bv 32 := 0x02813483.

(* [comment removed for export] *)
Definition W_dda6c : bv 32 := 0x02013903.

(* [comment removed for export] *)
Definition W_dda70 : bv 32 := 0x01813983.

(* [comment removed for export] *)
Definition W_dda74 : bv 32 := 0x01013a03.

(* [comment removed for export] *)
Definition W_dda78 : bv 32 := 0x00813a83.

(* [comment removed for export] *)
Definition W_dda7c : bv 32 := 0x04010113.

(* [comment removed for export] *)
Definition W_dda80 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dda84 : bv 32 := 0xff010113.

(* [comment removed for export] *)
Definition W_dda88 : bv 32 := 0x00113423.

(* [comment removed for export] *)
Definition W_dda8c : bv 32 := 0x00050e63.

(* [comment removed for export] *)
Definition W_dda90 : bv 32 := 0x00050593.

(* [comment removed for export] *)
Definition W_dda94 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dda98 : bv 32 := 0xc9c53503.

(* [comment removed for export] *)
Definition W_dda9c : bv 32 := 0x00800613.

(* [comment removed for export] *)
Definition W_ddaa0 : bv 32 := 0xf69860ef.

(* [comment removed for export] *)
Definition W_ddaa4 : bv 32 := 0x01c0006f.

(* [comment removed for export] *)
Definition W_ddaa8 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_ddaac : bv 32 := 0xc8853503.

(* [comment removed for export] *)
Definition W_ddab0 : bv 32 := 0x41c655b7.

(* [comment removed for export] *)
Definition W_ddab4 : bv 32 := 0xe6d5859b.

(* [comment removed for export] *)
Definition W_ddab8 : bv 32 := 0x02b505b3.

(* [comment removed for export] *)
Definition W_ddabc : bv 32 := 0x00b53023.

(* [comment removed for export] *)
Definition W_ddac0 : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_ddac4 : bv 32 := 0xc7053503.

(* [comment removed for export] *)
Definition W_ddac8 : bv 32 := 0x000500a3.

(* [comment removed for export] *)
Definition W_ddacc : bv 32 := 0x00053503.

(* [comment removed for export] *)
Definition W_ddad0 : bv 32 := 0x00020593.

(* [comment removed for export] *)
Definition W_ddad4 : bv 32 := 0xfea5b823.

(* [comment removed for export] *)
Definition W_ddad8 : bv 32 := 0x00813083.

(* [comment removed for export] *)
Definition W_ddadc : bv 32 := 0x01010113.

(* [comment removed for export] *)
Definition W_ddae0 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddae4 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_ddae8 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddaec : bv 32 := 0x00020513.

(* [comment removed for export] *)
Definition W_ddaf0 : bv 32 := 0xf5c50513.

(* [comment removed for export] *)
Definition W_ddaf4 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddaf8 : bv 32 := 0x00020593.

(* [comment removed for export] *)
Definition W_ddafc : bv 32 := 0x08453613.

(* [comment removed for export] *)
Definition W_ddb00 : bv 32 := 0x40c00633.

(* [comment removed for export] *)
Definition W_ddb04 : bv 32 := 0x00a67533.

(* [comment removed for export] *)
Definition W_ddb08 : bv 32 := 0xfff52617.

(* [comment removed for export] *)
Definition W_ddb0c : bv 32 := 0xfd05b583.

(* [comment removed for export] *)
Definition W_ddb10 : bv 32 := 0x00151513.

(* [comment removed for export] *)
Definition W_ddb14 : bv 32 := 0x6bc60613.

(* [comment removed for export] *)
Definition W_ddb18 : bv 32 := 0x00a60533.

(* [comment removed for export] *)
Definition W_ddb1c : bv 32 := 0x00055503.

(* [comment removed for export] *)
Definition W_ddb20 : bv 32 := 0x0285b583.

(* [comment removed for export] *)
Definition W_ddb24 : bv 32 := 0xfff52617.

(* [comment removed for export] *)
Definition W_ddb28 : bv 32 := 0xef860613.

(* [comment removed for export] *)
Definition W_ddb2c : bv 32 := 0x00a60533.

(* [comment removed for export] *)
Definition W_ddb30 : bv 32 := 0x2190006f.

(* [comment removed for export] *)
Definition W_ddb34 : bv 32 := 0xfd010113.

(* [comment removed for export] *)
Definition W_ddb38 : bv 32 := 0x02113423.

(* [comment removed for export] *)
Definition W_ddb3c : bv 32 := 0x00600513.

(* [comment removed for export] *)
Definition W_ddb40 : bv 32 := 0x7ad040ef.

(* [comment removed for export] *)
Definition W_ddb44 : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_ddb48 : bv 32 := 0x749040ef.

(* [comment removed for export] *)
Definition W_ddb4c : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_ddb50 : bv 32 := 0xbdc50513.

(* [comment removed for export] *)
Definition W_ddb54 : bv 32 := 0x38c0a0ef.

(* [comment removed for export] *)
Definition W_ddb58 : bv 32 := 0x00000613.

(* [comment removed for export] *)
Definition W_ddb5c : bv 32 := 0x00013423.

(* [comment removed for export] *)
Definition W_ddb60 : bv 32 := 0x00013823.

(* [comment removed for export] *)
Definition W_ddb64 : bv 32 := 0x00013c23.

(* [comment removed for export] *)
Definition W_ddb68 : bv 32 := 0x02013023.

(* [comment removed for export] *)
Definition W_ddb6c : bv 32 := 0x08600893.

(* [comment removed for export] *)
Definition W_ddb70 : bv 32 := 0x00600513.

(* [comment removed for export] *)
Definition W_ddb74 : bv 32 := 0x00810593.

(* [comment removed for export] *)
Definition W_ddb78 : bv 32 := 0x00800693.

(* [comment removed for export] *)
Definition W_ddb7c : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddb80 : bv 32 := 0x00020513.

(* [comment removed for export] *)
Definition W_ddb84 : bv 32 := 0xf5852503.

(* [comment removed for export] *)
Definition W_ddb88 : bv 32 := 0x02000613.

(* [comment removed for export] *)
Definition W_ddb8c : bv 32 := 0x08200893.

(* [comment removed for export] *)
Definition W_ddb90 : bv 32 := 0x00600593.

(* [comment removed for export] *)
Definition W_ddb94 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddb98 : bv 32 := 0x00c13023.

(* [comment removed for export] *)
Definition W_ddb9c : bv 32 := 0x08700893.

(* [comment removed for export] *)
Definition W_ddba0 : bv 32 := 0x00010593.

(* [comment removed for export] *)
Definition W_ddba4 : bv 32 := 0x00100513.

(* [comment removed for export] *)
Definition W_ddba8 : bv 32 := 0x00800693.

(* [comment removed for export] *)
Definition W_ddbac : bv 32 := 0x00000613.

(* [comment removed for export] *)
Definition W_ddbb0 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddbb4 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_ddbb8 : bv 32 := 0x00900513.

(* [comment removed for export] *)
Definition W_ddbbc : bv 32 := 0x731040ef.

(* [comment removed for export] *)
Definition W_ddbc0 : bv 32 := 0x07f00513.

(* [comment removed for export] *)
Definition W_ddbc4 : bv 32 := 0x004000ef.

(* [comment removed for export] *)
Definition W_ddbc8 : bv 32 := 0x00050593.
Lemma F_ddbc8 : fetch_word AsanUbsan.M.loaded_segments (0xe0f78 : word) = Some W_ddbc8.
Proof. vm_refl. Qed.
Lemma D_ddbc8 : decode_any W_ddbc8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbcc : bv 32 := 0x05e00893.
Lemma F_ddbcc : fetch_word AsanUbsan.M.loaded_segments (0xe0f7c : word) = Some W_ddbcc.
Proof. vm_refl. Qed.
Lemma D_ddbcc : decode_any W_ddbcc = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ddbd0 : bv 32 := 0x00000073.
Lemma F_ddbd0 : fetch_word AsanUbsan.M.loaded_segments (0xe0f80 : word) = Some W_ddbd0.
Proof. vm_refl. Qed.
Lemma E_ddbd0 : is_ecall W_ddbd0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ddbd4 : bv 32 := 0x05d00893.

(* [comment removed for export] *)
Definition W_ddbd8 : bv 32 := 0x00058513.

(* [comment removed for export] *)
Definition W_ddbdc : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddbe0 : bv 32 := 0xff9ff06f.

(* [comment removed for export] *)
Definition W_ddbe4 : bv 32 := 0xff010113.

(* [comment removed for export] *)
Definition W_ddbe8 : bv 32 := 0x00113423.

(* [comment removed for export] *)
Definition W_ddbec : bv 32 := 0x00068713.

(* [comment removed for export] *)
Definition W_ddbf0 : bv 32 := 0x00060793.

(* [comment removed for export] *)
Definition W_ddbf4 : bv 32 := 0x00058693.

(* [comment removed for export] *)
Definition W_ddbf8 : bv 32 := 0x00050613.

(* [comment removed for export] *)
Definition W_ddbfc : bv 32 := 0x00019517.

(* [comment removed for export] *)
Definition W_ddc00 : bv 32 := 0xfff37597.

(* [comment removed for export] *)
Definition W_ddc04 : bv 32 := 0x4dc50513.

(* [comment removed for export] *)
Definition W_ddc08 : bv 32 := 0xea858593.

(* [comment removed for export] *)
Definition W_ddc0c : bv 32 := 0xf70770ef.

(* [comment removed for export] *)
Definition W_ddc10 : bv 32 := 0xf25ff0ef.

(* [comment removed for export] *)
Definition W_ddc14 : bv 32 := 0xfd010113.

(* [comment removed for export] *)
Definition W_ddc18 : bv 32 := 0x02113423.

(* [comment removed for export] *)
Definition W_ddc1c : bv 32 := 0x02813023.

(* [comment removed for export] *)
Definition W_ddc20 : bv 32 := 0x00913c23.

(* [comment removed for export] *)
Definition W_ddc24 : bv 32 := 0x01213823.

(* [comment removed for export] *)
Definition W_ddc28 : bv 32 := 0x01313423.

(* [comment removed for export] *)
Definition W_ddc2c : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_ddc30 : bv 32 := 0xb0450913.

(* [comment removed for export] *)
Definition W_ddc34 : bv 32 := 0x00490413.

(* [comment removed for export] *)
Definition W_ddc38 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddc3c : bv 32 := 0x2a40a0ef.

(* [comment removed for export] *)
Definition W_ddc40 : bv 32 := 0x01093503.

(* [comment removed for export] *)
Definition W_ddc44 : bv 32 := 0x06050863.

(* [comment removed for export] *)
Definition W_ddc48 : bv 32 := 0x00892583.

(* [comment removed for export] *)
Definition W_ddc4c : bv 32 := 0x0180006f.

(* [comment removed for export] *)
Definition W_ddc50 : bv 32 := 0x00053503.

(* [comment removed for export] *)
Definition W_ddc54 : bv 32 := 0x02000593.

(* [comment removed for export] *)
Definition W_ddc58 : bv 32 := 0x00b92423.

(* [comment removed for export] *)
Definition W_ddc5c : bv 32 := 0x00a93823.

(* [comment removed for export] *)
Definition W_ddc60 : bv 32 := 0x04050a63.

(* [comment removed for export] *)
Definition W_ddc64 : bv 32 := 0xfff5861b.

(* [comment removed for export] *)
Definition W_ddc68 : bv 32 := 0x00c92423.

(* [comment removed for export] *)
Definition W_ddc6c : bv 32 := 0xfeb052e3.

(* [comment removed for export] *)
Definition W_ddc70 : bv 32 := 0x01093503.

(* [comment removed for export] *)
Definition W_ddc74 : bv 32 := 0x00361613.

(* [comment removed for export] *)
Definition W_ddc78 : bv 32 := 0x00c50533.

(* [comment removed for export] *)
Definition W_ddc7c : bv 32 := 0x00853983.

(* [comment removed for export] *)
Definition W_ddc80 : bv 32 := 0x10853483.

(* [comment removed for export] *)
Definition W_ddc84 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddc88 : bv 32 := 0x4e00a0ef.

(* [comment removed for export] *)
Definition W_ddc8c : bv 32 := 0x00048513.

(* [comment removed for export] *)
Definition W_ddc90 : bv 32 := 0x000980e7.

(* [comment removed for export] *)
Definition W_ddc94 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddc98 : bv 32 := 0x2480a0ef.

(* [comment removed for export] *)
Definition W_ddc9c : bv 32 := 0x00892503.

(* [comment removed for export] *)
Definition W_ddca0 : bv 32 := 0xfff5061b.

(* [comment removed for export] *)
Definition W_ddca4 : bv 32 := 0x00c92423.

(* [comment removed for export] *)
Definition W_ddca8 : bv 32 := 0xfca044e3.

(* [comment removed for export] *)
Definition W_ddcac : bv 32 := 0x01093503.

(* [comment removed for export] *)
Definition W_ddcb0 : bv 32 := 0xfa1ff06f.

(* [comment removed for export] *)
Definition W_ddcb4 : bv 32 := 0x00100513.

(* [comment removed for export] *)
Definition W_ddcb8 : bv 32 := 0x00a90023.

(* [comment removed for export] *)
Definition W_ddcbc : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddcc0 : bv 32 := 0x02813083.

(* [comment removed for export] *)
Definition W_ddcc4 : bv 32 := 0x02013403.

(* [comment removed for export] *)
Definition W_ddcc8 : bv 32 := 0x01813483.

(* [comment removed for export] *)
Definition W_ddccc : bv 32 := 0x01013903.

(* [comment removed for export] *)
Definition W_ddcd0 : bv 32 := 0x00813983.

(* [comment removed for export] *)
Definition W_ddcd4 : bv 32 := 0x03010113.

(* [comment removed for export] *)
Definition W_ddcd8 : bv 32 := 0x4900a06f.

(* [comment removed for export] *)
Definition W_ddcdc : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddce0 : bv 32 := 0xfd010113.

(* [comment removed for export] *)
Definition W_ddce4 : bv 32 := 0x02113423.

(* [comment removed for export] *)
Definition W_ddce8 : bv 32 := 0x02813023.

(* [comment removed for export] *)
Definition W_ddcec : bv 32 := 0x00913c23.

(* [comment removed for export] *)
Definition W_ddcf0 : bv 32 := 0x01213823.

(* [comment removed for export] *)
Definition W_ddcf4 : bv 32 := 0x01313423.

(* [comment removed for export] *)
Definition W_ddcf8 : bv 32 := 0x00050493.

(* [comment removed for export] *)
Definition W_ddcfc : bv 32 := 0x0057c517.

(* [comment removed for export] *)
Definition W_ddd00 : bv 32 := 0xa3450993.

(* [comment removed for export] *)
Definition W_ddd04 : bv 32 := 0x00498413.

(* [comment removed for export] *)
Definition W_ddd08 : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddd0c : bv 32 := 0x1d40a0ef.

(* [comment removed for export] *)
Definition W_ddd10 : bv 32 := 0x0009c503.

(* [comment removed for export] *)
Definition W_ddd14 : bv 32 := 0xfff00913.

(* [comment removed for export] *)
Definition W_ddd18 : bv 32 := 0x06051263.

(* [comment removed for export] *)
Definition W_ddd1c : bv 32 := 0x0109b503.

(* [comment removed for export] *)
Definition W_ddd20 : bv 32 := 0x00051663.

(* [comment removed for export] *)
Definition W_ddd24 : bv 32 := 0x01898513.

(* [comment removed for export] *)
Definition W_ddd28 : bv 32 := 0x00a9b823.

(* [comment removed for export] *)
Definition W_ddd2c : bv 32 := 0x0089a583.

(* [comment removed for export] *)
Definition W_ddd30 : bv 32 := 0x02000613.

(* [comment removed for export] *)
Definition W_ddd34 : bv 32 := 0x02c59263.

(* [comment removed for export] *)
Definition W_ddd38 : bv 32 := 0x20800513.

(* [comment removed for export] *)
Definition W_ddd3c : bv 32 := 0x00100593.

(* [comment removed for export] *)
Definition W_ddd40 : bv 32 := 0x3b5000ef.

(* [comment removed for export] *)
Definition W_ddd44 : bv 32 := 0x02050c63.

(* [comment removed for export] *)
Definition W_ddd48 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_ddd4c : bv 32 := 0x0109b603.

(* [comment removed for export] *)
Definition W_ddd50 : bv 32 := 0x00c53023.

(* [comment removed for export] *)
Definition W_ddd54 : bv 32 := 0x00a9b823.

(* [comment removed for export] *)
Definition W_ddd58 : bv 32 := 0x00000913.

(* [comment removed for export] *)
Definition W_ddd5c : bv 32 := 0x00359613.

(* [comment removed for export] *)
Definition W_ddd60 : bv 32 := 0x00c50533.

(* [comment removed for export] *)
Definition W_ddd64 : bv 32 := 0x00000617.

(* [comment removed for export] *)
Definition W_ddd68 : bv 32 := 0x00158593.

(* [comment removed for export] *)
Definition W_ddd6c : bv 32 := 0x04060613.

(* [comment removed for export] *)
Definition W_ddd70 : bv 32 := 0x00c53423.

(* [comment removed for export] *)
Definition W_ddd74 : bv 32 := 0x10953423.

(* [comment removed for export] *)
Definition W_ddd78 : bv 32 := 0x00b9a423.

(* [comment removed for export] *)
Definition W_ddd7c : bv 32 := 0x00040513.

(* [comment removed for export] *)
Definition W_ddd80 : bv 32 := 0x3e80a0ef.

(* [comment removed for export] *)
Definition W_ddd84 : bv 32 := 0x00090513.

(* [comment removed for export] *)
Definition W_ddd88 : bv 32 := 0x02813083.

(* [comment removed for export] *)
Definition W_ddd8c : bv 32 := 0x02013403.

(* [comment removed for export] *)
Definition W_ddd90 : bv 32 := 0x01813483.

(* [comment removed for export] *)
Definition W_ddd94 : bv 32 := 0x01013903.

(* [comment removed for export] *)
Definition W_ddd98 : bv 32 := 0x00813983.

(* [comment removed for export] *)
Definition W_ddd9c : bv 32 := 0x03010113.

(* [comment removed for export] *)
Definition W_ddda0 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddda4 : bv 32 := 0x00050067.

(* [comment removed for export] *)
Definition W_ddda8 : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_dddac : bv 32 := 0xfe010113.

(* [comment removed for export] *)
Definition W_dddb0 : bv 32 := 0x00113c23.

(* [comment removed for export] *)
Definition W_dddb4 : bv 32 := 0x00813823.

(* [comment removed for export] *)
Definition W_dddb8 : bv 32 := 0x00913423.

(* [comment removed for export] *)
Definition W_dddbc : bv 32 := 0x00016517.

(* [comment removed for export] *)
Definition W_dddc0 : bv 32 := 0x00016597.

(* [comment removed for export] *)
Definition W_dddc4 : bv 32 := 0x9a453503.

(* [comment removed for export] *)
Definition W_dddc8 : bv 32 := 0x9a85b403.

(* [comment removed for export] *)
Definition W_dddcc : bv 32 := 0x00a47c63.

(* [comment removed for export] *)
Definition W_dddd0 : bv 32 := 0xff853583.

(* [comment removed for export] *)
Definition W_dddd4 : bv 32 := 0xff850493.

(* [comment removed for export] *)
Definition W_dddd8 : bv 32 := 0x000580e7.

(* [comment removed for export] *)
Definition W_ddddc : bv 32 := 0x00048513.

(* [comment removed for export] *)
Definition W_ddde0 : bv 32 := 0xfe9468e3.

(* [comment removed for export] *)
Definition W_ddde4 : bv 32 := 0x01813083.

(* [comment removed for export] *)
Definition W_ddde8 : bv 32 := 0x01013403.

(* [comment removed for export] *)
Definition W_dddec : bv 32 := 0x00813483.

(* [comment removed for export] *)
Definition W_dddf0 : bv 32 := 0x02010113.

(* [comment removed for export] *)
Definition W_dddf4 : bv 32 := 0xfb5ff06f.

(* [comment removed for export] *)
Definition W_dddf8 : bv 32 := 0xff010113.

(* [comment removed for export] *)
Definition W_dddfc : bv 32 := 0x00113423.

(* [comment removed for export] *)
Definition W_dde00 : bv 32 := 0x00813023.

(* [comment removed for export] *)
Definition W_dde04 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_dde08 : bv 32 := 0x00020613.

(* [comment removed for export] *)
Definition W_dde0c : bv 32 := 0xf5862603.

(* [comment removed for export] *)
Definition W_dde10 : bv 32 := 0x0057c697.

(* [comment removed for export] *)
Definition W_dde14 : bv 32 := 0xb4068693.

(* [comment removed for export] *)
Definition W_dde18 : bv 32 := 0x1606a72f.

(* [comment removed for export] *)
Definition W_dde1c : bv 32 := 0x00b71663.

(* [comment removed for export] *)
Definition W_dde20 : bv 32 := 0x1ec6a7af.

(* [comment removed for export] *)
Definition W_dde24 : bv 32 := 0xfe079ae3.

(* [comment removed for export] *)
Definition W_dde28 : bv 32 := 0x0007059b.

(* [comment removed for export] *)
Definition W_dde2c : bv 32 := 0x02c58263.

(* [comment removed for export] *)
Definition W_dde30 : bv 32 := 0x02058263.

(* [comment removed for export] *)
Definition W_dde34 : bv 32 := 0x04900893.

(* [comment removed for export] *)
Definition W_dde38 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_dde3c : bv 32 := 0x00000613.

(* [comment removed for export] *)
Definition W_dde40 : bv 32 := 0x00000693.

(* [comment removed for export] *)
Definition W_dde44 : bv 32 := 0x00000513.

(* [comment removed for export] *)
Definition W_dde48 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_dde4c : bv 32 := 0xff9ff06f.

(* [comment removed for export] *)
Definition W_dde50 : bv 32 := 0x00000023.

(* [comment removed for export] *)
Definition W_dde54 : bv 32 := 0x00050413.

(* [comment removed for export] *)
Definition W_dde58 : bv 32 := 0xdbdff0ef.

(* [comment removed for export] *)
Definition W_dde5c : bv 32 := 0xf51ff0ef.

(* [comment removed for export] *)
Definition W_dde60 : bv 32 := 0x289050ef.

(* [comment removed for export] *)
Definition W_dde64 : bv 32 := 0x00040513.
Lemma F_dde64 : fetch_word AsanUbsan.M.loaded_segments (0xe1214 : word) = Some W_dde64.
Proof. vm_refl. Qed.
Lemma D_dde64 : decode_any W_dde64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dde68 : bv 32 := 0xd61ff0ef.
Lemma F_dde68 : fetch_word AsanUbsan.M.loaded_segments (0xe1218 : word) = Some W_dde68.
Proof. vm_refl. Qed.
Lemma D_dde68 : decode_any W_dde68 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_dde6c : bv 32 := 0xfa010113.

(* [comment removed for export] *)
Definition W_dde70 : bv 32 := 0x02113423.

(* [comment removed for export] *)
Definition W_dde74 : bv 32 := 0x02813023.

(* [comment removed for export] *)
Definition W_dde78 : bv 32 := 0x05013823.

(* [comment removed for export] *)
Definition W_dde7c : bv 32 := 0x05113c23.

(* [comment removed for export] *)
Definition W_dde80 : bv 32 := 0x00016817.

(* [comment removed for export] *)
Definition W_dde84 : bv 32 := 0x8b083403.

(* [comment removed for export] *)
Definition W_dde88 : bv 32 := 0x02c13823.

(* [comment removed for export] *)
Definition W_dde8c : bv 32 := 0x02d13c23.

(* [comment removed for export] *)
Definition W_dde90 : bv 32 := 0x04e13023.

(* [comment removed for export] *)
Definition W_dde94 : bv 32 := 0x04f13423.

(* [comment removed for export] *)
Definition W_dde98 : bv 32 := 0x00043683.

(* [comment removed for export] *)
Definition W_dde9c : bv 32 := 0x03810713.

(* [comment removed for export] *)
Definition W_ddea0 : bv 32 := 0x01000793.

(* [comment removed for export] *)
Definition W_ddea4 : bv 32 := 0x00d13c23.

(* [comment removed for export] *)
Definition W_ddea8 : bv 32 := 0x00e13823.

(* [comment removed for export] *)
Definition W_ddeac : bv 32 := 0x08b7ea63.

(* [comment removed for export] *)
Definition W_ddeb0 : bv 32 := 0x000186b7.

(* [comment removed for export] *)
Definition W_ddeb4 : bv 32 := 0x0606869b.

(* [comment removed for export] *)
Definition W_ddeb8 : bv 32 := 0x00b6d6b3.

(* [comment removed for export] *)
Definition W_ddebc : bv 32 := 0x0016f693.

(* [comment removed for export] *)
Definition W_ddec0 : bv 32 := 0x02068863.

(* [comment removed for export] *)
Definition W_ddec4 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddec8 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddecc : bv 32 := 0x284000ef.

(* [comment removed for export] *)
Definition W_dded0 : bv 32 := 0x00043583.

(* [comment removed for export] *)
Definition W_dded4 : bv 32 := 0x01813603.

(* [comment removed for export] *)
Definition W_dded8 : bv 32 := 0x18c59863.

(* [comment removed for export] *)
Definition W_ddedc : bv 32 := 0x0005051b.

(* [comment removed for export] *)
Definition W_ddee0 : bv 32 := 0x02813083.

(* [comment removed for export] *)
Definition W_ddee4 : bv 32 := 0x02013403.

(* [comment removed for export] *)
Definition W_ddee8 : bv 32 := 0x06010113.

(* [comment removed for export] *)
Definition W_ddeec : bv 32 := 0x00008067.

(* [comment removed for export] *)
Definition W_ddef0 : bv 32 := 0x00700693.

(* [comment removed for export] *)
Definition W_ddef4 : bv 32 := 0x0ed58a63.

(* [comment removed for export] *)
Definition W_ddef8 : bv 32 := 0x00900693.

(* [comment removed for export] *)
Definition W_ddefc : bv 32 := 0x04d59263.

(* [comment removed for export] *)
Definition W_ddf00 : bv 32 := 0x00060693.

(* [comment removed for export] *)
Definition W_ddf04 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddf08 : bv 32 := 0x01000593.

(* [comment removed for export] *)
Definition W_ddf0c : bv 32 := 0x00810613.

(* [comment removed for export] *)
Definition W_ddf10 : bv 32 := 0x00050713.

(* [comment removed for export] *)
Definition W_ddf14 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddf18 : bv 32 := 0x0005051b.

(* [comment removed for export] *)
Definition W_ddf1c : bv 32 := 0x10050a63.

(* [comment removed for export] *)
Definition W_ddf20 : bv 32 := 0xfea00593.

(* [comment removed for export] *)
Definition W_ddf24 : bv 32 := 0xfab514e3.

(* [comment removed for export] *)
Definition W_ddf28 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddf2c : bv 32 := 0x00900593.

(* [comment removed for export] *)
Definition W_ddf30 : bv 32 := 0x00070513.

(* [comment removed for export] *)
Definition W_ddf34 : bv 32 := 0x00068613.

(* [comment removed for export] *)
Definition W_ddf38 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddf3c : bv 32 := 0xf95ff06f.

(* [comment removed for export] *)
Definition W_ddf40 : bv 32 := 0x40600693.

(* [comment removed for export] *)
Definition W_ddf44 : bv 32 := 0x08d59463.

(* [comment removed for export] *)
Definition W_ddf48 : bv 32 := 0x00050793.

(* [comment removed for export] *)
Definition W_ddf4c : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddf50 : bv 32 := 0x40600593.

(* [comment removed for export] *)
Definition W_ddf54 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddf58 : bv 32 := 0x0005071b.

(* [comment removed for export] *)
Definition W_ddf5c : bv 32 := 0xfea00813.

(* [comment removed for export] *)
Definition W_ddf60 : bv 32 := 0x0b071663.

(* [comment removed for export] *)
Definition W_ddf64 : bv 32 := 0x00060693.

(* [comment removed for export] *)
Definition W_ddf68 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddf6c : bv 32 := 0x40600593.

(* [comment removed for export] *)
Definition W_ddf70 : bv 32 := 0x00078513.

(* [comment removed for export] *)
Definition W_ddf74 : bv 32 := 0x00000613.

(* [comment removed for export] *)
Definition W_ddf78 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddf7c : bv 32 := 0x0005059b.

(* [comment removed for export] *)
Definition W_ddf80 : bv 32 := 0x0d059463.

(* [comment removed for export] *)
Definition W_ddf84 : bv 32 := 0x00078513.

(* [comment removed for export] *)
Definition W_ddf88 : bv 32 := 0x00000593.

(* [comment removed for export] *)
Definition W_ddf8c : bv 32 := 0x00068613.

(* [comment removed for export] *)
Definition W_ddf90 : bv 32 := 0x800006b7.

(* [comment removed for export] *)
Definition W_ddf94 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddf98 : bv 32 := 0xfff6869b.

(* [comment removed for export] *)
Definition W_ddf9c : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddfa0 : bv 32 := 0x00050713.

(* [comment removed for export] *)
Definition W_ddfa4 : bv 32 := 0x00168513.

(* [comment removed for export] *)
Definition W_ddfa8 : bv 32 := 0x00a77533.

(* [comment removed for export] *)
Definition W_ddfac : bv 32 := 0x00051c63.

(* [comment removed for export] *)
Definition W_ddfb0 : bv 32 := 0x00d77533.

(* [comment removed for export] *)
Definition W_ddfb4 : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddfb8 : bv 32 := 0x00200593.

(* [comment removed for export] *)
Definition W_ddfbc : bv 32 := 0x00100613.

(* [comment removed for export] *)
Definition W_ddfc0 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddfc4 : bv 32 := 0x0007071b.

(* [comment removed for export] *)
Definition W_ddfc8 : bv 32 := 0x0980006f.

(* [comment removed for export] *)
Definition W_ddfcc : bv 32 := 0xffc58693.

(* [comment removed for export] *)
Definition W_ddfd0 : bv 32 := 0x0016b693.

(* [comment removed for export] *)
Definition W_ddfd4 : bv 32 := 0x00f69693.

(* [comment removed for export] *)
Definition W_ddfd8 : bv 32 := 0x00d66633.

(* [comment removed for export] *)
Definition W_ddfdc : bv 32 := 0x01900893.

(* [comment removed for export] *)
Definition W_ddfe0 : bv 32 := 0x00000073.

(* [comment removed for export] *)
Definition W_ddfe4 : bv 32 := 0xee9ff06f.

(* [comment removed for export] *)
Definition W_ddfe8 : bv 32 := 0x00050593.

(* [comment removed for export] *)
Definition W_ddfec : bv 32 := 0x01900513.

(* [comment removed for export] *)
Definition W_ddff0 : bv 32 := 0x00060693.

(* [comment removed for export] *)
Definition W_ddff4 : bv 32 := 0x00700613.

(* [comment removed for export] *)
Definition W_ddff8 : bv 32 := 0x00000713.

(* [comment removed for export] *)
Definition W_ddffc : bv 32 := 0x00000793.
