(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YG00 YG01 YG0h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK11 YN05.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YB0z YB0u YB0x YB10 YF8z YF90.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require YB1u YB1p YB1s YB1v YF9i YF9j.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Asan AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Inductive img : Set := K_tra | K_trb.
Existing Class img.
Section g.
Context {imgk : img}.
Definition D_m8 : Z := match imgk with K_tra => 0 | K_trb => (-8) end.
Definition D_8 : Z := match imgk with K_tra => 0 | K_trb => 0x8 end.
Definition D_m9 : Z := match imgk with K_tra => 0 | K_trb => (-9) end.
Definition D_10 : Z := match imgk with K_tra => 0 | K_trb => 0x10 end.
Definition D_18 : Z := match imgk with K_tra => 0 | K_trb => 0x18 end.
Definition D_20 : Z := match imgk with K_tra => 0 | K_trb => 0x20 end.
Definition D_30 : Z := match imgk with K_tra => 0 | K_trb => 0x30 end.
Definition D_m3c : Z := match imgk with K_tra => 0 | K_trb => (-60) end.
Definition D_m3e : Z := match imgk with K_tra => 0 | K_trb => (-62) end.
Definition D_m40 : Z := match imgk with K_tra => 0 | K_trb => (-64) end.
Definition D_4e : Z := match imgk with K_tra => 0 | K_trb => 0x4e end.
Definition D_50 : Z := match imgk with K_tra => 0 | K_trb => 0x50 end.
Definition D_6c : Z := match imgk with K_tra => 0 | K_trb => 0x6c end.
Definition D_a0 : Z := match imgk with K_tra => 0 | K_trb => 0xa0 end.
Definition D_150 : Z := match imgk with K_tra => 0 | K_trb => 0x150 end.
Definition D_200 : Z := match imgk with K_tra => 0 | K_trb => 0x200 end.
Definition D_218 : Z := match imgk with K_tra => 0 | K_trb => 0x218 end.
Definition D_21c : Z := match imgk with K_tra => 0 | K_trb => 0x21c end.
Definition D_21e : Z := match imgk with K_tra => 0 | K_trb => 0x21e end.
Definition D_220 : Z := match imgk with K_tra => 0 | K_trb => 0x220 end.
Definition D_270 : Z := match imgk with K_tra => 0 | K_trb => 0x270 end.
Definition D_274 : Z := match imgk with K_tra => 0 | K_trb => 0x274 end.
Definition D_280 : Z := match imgk with K_tra => 0 | K_trb => 0x280 end.
Definition D_2b4 : Z := match imgk with K_tra => 0 | K_trb => 0x2b4 end.
Definition D_2c4 : Z := match imgk with K_tra => 0 | K_trb => 0x2c4 end.
Definition D_2cc : Z := match imgk with K_tra => 0 | K_trb => 0x2cc end.
Definition D_m3ac : Z := match imgk with K_tra => 0 | K_trb => (-940) end.
Definition D_430 : Z := match imgk with K_tra => 0 | K_trb => 0x430 end.
Definition D_440 : Z := match imgk with K_tra => 0 | K_trb => 0x440 end.
Definition D_a2c : Z := match imgk with K_tra => 0 | K_trb => 0xa2c end.
Definition D_1000 : Z := match imgk with K_tra => 0 | K_trb => 0x1000 end.
Definition D_104c : Z := match imgk with K_tra => 0 | K_trb => 0x104c end.
Definition D_10c0 : Z := match imgk with K_tra => 0 | K_trb => 0x10c0 end.
Definition D_10e0 : Z := match imgk with K_tra => 0 | K_trb => 0x10e0 end.
Definition D_10e8 : Z := match imgk with K_tra => 0 | K_trb => 0x10e8 end.
Definition D_10ec : Z := match imgk with K_tra => 0 | K_trb => 0x10ec end.
Definition D_10f0 : Z := match imgk with K_tra => 0 | K_trb => 0x10f0 end.
Definition D_1100 : Z := match imgk with K_tra => 0 | K_trb => 0x1100 end.
Definition D_54c0 : Z := match imgk with K_tra => 0 | K_trb => 0x54c0 end.
Definition D_5680 : Z := match imgk with K_tra => 0 | K_trb => 0x5680 end.
Definition D_m27b919177701d40 : Z := match imgk with K_tra => 0 | K_trb => (-178896664171388224) end.
Definition D_m10c55b69b38ab717 : Z := match imgk with K_tra => 0 | K_trb => (-1208472584560752407) end.
Definition D_m261b33dfb1afee1d : Z := match imgk with K_tra => 0 | K_trb => (-2745845433664269853) end.
Definition D_332fe4d8b3da5a5b : Z := match imgk with K_tra => 0 | K_trb => 0x332fe4d8b3da5a5b end.
Definition D_558ab28b2f16c771 : Z := match imgk with K_tra => 0 | K_trb => 0x558ab28b2f16c771 end.
Definition D_m5c6cf5c3c23d561f : Z := match imgk with K_tra => 0 | K_trb => (-6659968170100348447) end.
Definition D_ma7775317fd2cb971 : Z := match imgk with K_tra => 0 | K_trb => (-12067205089059453297) end.
Definition D_mcf6373b41df84414 : Z := match imgk with K_tra => 0 | K_trb => (-14943915205979554836) end.
End g.
Definition seln {T : Type} (k : img) (a1 a2 : T) : T := match k with K_tra => a1 | K_trb => a2 end.
Definition zplus (a b : Z) : Z := a + b.
Definition dsel (k : img) (d : Z) : option Z :=
if d =? (-8) then Some (@D_m8 k) else if d =? (8) then Some (@D_8 k) else if d =? (-9) then Some (@D_m9 k) else if d =? (16) then Some (@D_10 k) else if d =? (24) then Some (@D_18 k) else if d =? (32) then Some (@D_20 k) else if d =? (48) then Some (@D_30 k) else if d =? (-60) then Some (@D_m3c k) else if d =? (-62) then Some (@D_m3e k) else if d =? (-64) then Some (@D_m40 k) else if d =? (78) then Some (@D_4e k) else if d =? (80) then Some (@D_50 k) else if d =? (108) then Some (@D_6c k) else if d =? (160) then Some (@D_a0 k) else if d =? (336) then Some (@D_150 k) else if d =? (512) then Some (@D_200 k) else if d =? (536) then Some (@D_218 k) else if d =? (540) then Some (@D_21c k) else if d =? (542) then Some (@D_21e k) else if d =? (544) then Some (@D_220 k) else if d =? (624) then Some (@D_270 k) else if d =? (628) then Some (@D_274 k) else if d =? (640) then Some (@D_280 k) else if d =? (692) then Some (@D_2b4 k) else if d =? (708) then Some (@D_2c4 k) else if d =? (716) then Some (@D_2cc k) else if d =? (-940) then Some (@D_m3ac k) else if d =? (1072) then Some (@D_430 k) else if d =? (1088) then Some (@D_440 k) else if d =? (2604) then Some (@D_a2c k) else if d =? (4096) then Some (@D_1000 k) else if d =? (4172) then Some (@D_104c k) else if d =? (4288) then Some (@D_10c0 k) else if d =? (4320) then Some (@D_10e0 k) else if d =? (4328) then Some (@D_10e8 k) else if d =? (4332) then Some (@D_10ec k) else if d =? (4336) then Some (@D_10f0 k) else if d =? (4352) then Some (@D_1100 k) else if d =? (21696) then Some (@D_54c0 k) else if d =? (22144) then Some (@D_5680 k) else if d =? (-178896664171388224) then Some (@D_m27b919177701d40 k) else if d =? (-1208472584560752407) then Some (@D_m10c55b69b38ab717 k) else if d =? (-2745845433664269853) then Some (@D_m261b33dfb1afee1d k) else if d =? (3688418239221226075) then Some (@D_332fe4d8b3da5a5b k) else if d =? (6163935350870165361) then Some (@D_558ab28b2f16c771 k) else if d =? (-6659968170100348447) then Some (@D_m5c6cf5c3c23d561f k) else if d =? (-12067205089059453297) then Some (@D_ma7775317fd2cb971 k) else if d =? (-14943915205979554836) then Some (@D_mcf6373b41df84414 k) else None.
Definition zsel (k : img) (a1 a2 : Z) : Z :=
if Z.eqb a1 a2 then a1 else
match dsel k (a2 - a1) with Some D => zplus a1 D | None => seln k a1 a2 end.
Ltac img_cbv t := let t1 := eval cbv -[zplus D_m8 D_8 D_m9 D_10 D_18 D_20 D_30 D_m3c D_m3e D_m40 D_4e D_50 D_6c D_a0 D_150 D_200 D_218 D_21c D_21e D_220 D_270 D_274 D_280 D_2b4 D_2c4 D_2cc D_m3ac D_430 D_440 D_a2c D_1000 D_104c D_10c0 D_10e0 D_10e8 D_10ec D_10f0 D_1100 D_54c0 D_5680 D_m27b919177701d40 D_m10c55b69b38ab717 D_m261b33dfb1afee1d D_332fe4d8b3da5a5b D_558ab28b2f16c771 D_m5c6cf5c3c23d561f D_ma7775317fd2cb971 D_mcf6373b41df84414] in t in eval cbv beta delta [zplus] in t1.
Ltac img_head t := lazymatch t with ?f _ => img_head f | _ => t end.
Ltac img_merge_gen k v1 v2 :=
lazymatch v1 with
| v2 => v1
| _ =>
let T := type of v1 in
lazymatch T with
| Z => img_cbv (zsel k v1 v2)
| nat => constr:(seln k v1 v2) | positive => constr:(seln k v1 v2) | N => constr:(seln k v1 v2) | bool => constr:(seln k v1 v2)
| _ =>
let h1 := img_head v1 in let h2 := img_head v2 in
lazymatch h1 with
| h2 =>
lazymatch v1 with
| ?f1 ?a1 => lazymatch v2 with
| ?f2 ?a2 => let f := img_merge_gen k f1 f2 in let a := img_merge_gen k a1 a2 in constr:(f a)
| _ => constr:(seln k v1 v2)
end
| _ => constr:(seln k v1 v2)
end
| _ => constr:(seln k v1 v2)
end
end
end.
Section i.
Context {imgk : img}.
Definition tfx_loaded_segments : list Segment := match imgk with K_tra => Asan.M.loaded_segments | K_trb => AsanUbsan.M.loaded_segments end.
Definition tfxguard_count := match imgk with K_tra => YB0z.traguard_count | K_trb => YB1u.trbguard_count end.
Definition tfxguard_start : Z := 0x80f34 + D_2c4.
Definition tfxmusl_tbl := match imgk with K_tra => YB0z.tramusl_tbl | K_trb => YB1u.trbmusl_tbl end.
Definition tfxmusl_text_count := match imgk with K_tra => YB0z.tramusl_text_count | K_trb => YB1u.trbmusl_text_count end.
Definition tfxmusl_text_start : Z := 0x90bb8 + D_104c.
Definition tfxsegs : list Segment := tfx_loaded_segments.
Definition tfxtbl_rtA := match imgk with K_tra => YB0u.tratbl_rtA | K_trb => YB1p.trbtbl_rtA end.
Definition tfxtbl_rtA_build := match imgk with K_tra => YB0u.tratbl_rtA_build | K_trb => YB1p.trbtbl_rtA_build end.
Definition tfxtbl_rtB := match imgk with K_tra => YB0u.tratbl_rtB | K_trb => YB1p.trbtbl_rtB end.
Definition tfxtbl_rtB_build := match imgk with K_tra => YB0u.tratbl_rtB_build | K_trb => YB1p.trbtbl_rtB_build end.
Definition tfxtbl_rtC := match imgk with K_tra => YB0u.tratbl_rtC | K_trb => YB1p.trbtbl_rtC end.
Definition tfxtbl_rtC_build := match imgk with K_tra => YB0u.tratbl_rtC_build | K_trb => YB1p.trbtbl_rtC_build end.
Definition tfxtbl_rtD := match imgk with K_tra => YB0u.tratbl_rtD | K_trb => YB1p.trbtbl_rtD end.
Definition tfxtbl_rtD_build := match imgk with K_tra => YB0u.tratbl_rtD_build | K_trb => YB1p.trbtbl_rtD_build end.
Definition tfxtbl_rtF := match imgk with K_tra => YB0x.tratbl_rtF | K_trb => YB1s.trbtbl_rtF end.
Definition tfxtbl_rtF_build := match imgk with K_tra => YB0x.tratbl_rtF_build | K_trb => YB1s.trbtbl_rtF_build end.
Definition tfxtbl_rtG := match imgk with K_tra => YB0x.tratbl_rtG | K_trb => YB1s.trbtbl_rtG end.
Definition tfxtbl_rtG_build := match imgk with K_tra => YB0x.tratbl_rtG_build | K_trb => YB1s.trbtbl_rtG_build end.
Definition tfxtbl_rtK := match imgk with K_tra => YB0x.tratbl_rtK | K_trb => YB1s.trbtbl_rtK end.
Definition tfxtbl_rtK_build := match imgk with K_tra => YB0x.tratbl_rtK_build | K_trb => YB1s.trbtbl_rtK_build end.
Definition tfxtbl_rtM := match imgk with K_tra => YB0x.tratbl_rtM | K_trb => YB1s.trbtbl_rtM end.
Definition tfxtbl_rtM_build := match imgk with K_tra => YB0x.tratbl_rtM_build | K_trb => YB1s.trbtbl_rtM_build end.
Definition tfx_A_musl_memchr : Z := 0x9b394 + D_10ec.
Definition tfx_A_musl_memcmp : Z := 0x9b460 + D_10ec.
Definition tfx_A_musl_memcpy : Z := 0x9b490 + D_10ec.
Definition tfx_A_musl_memset : Z := 0x9b894 + D_10ec.
Definition tfx_A_musl_strnlen : Z := 0x9bd1c + D_10ec.
Definition tfx_segment_000 := match imgk with K_tra => Asan.Asan_segment_000 | K_trb => AsanUbsan.AsanUbsan_segment_000 end.
Definition tfx_segment_001 := match imgk with K_tra => Asan.Asan_segment_001 | K_trb => AsanUbsan.AsanUbsan_segment_001 end.
Definition tfx_segment_002 := match imgk with K_tra => Asan.Asan_segment_002 | K_trb => AsanUbsan.AsanUbsan_segment_002 end.
Definition tfx_segment_003 := match imgk with K_tra => Asan.Asan_segment_003 | K_trb => AsanUbsan.AsanUbsan_segment_003 end.
Definition Tfx_code : acode := {|
pc_malloc := (0x532dc + D_2c4);        pc_wrap_malloc := (0x53104 + D_2c4);   pc_malloc_ra0 := (0x533a4 + D_2c4);
pc_free := (0x5310c + D_2c4);          pc_wrap_free := (0x53100 + D_2c4);     pc_free_ra0 := (0x53244 + D_2c4);
pc_stack_malloc := fun cid => if cid =? 1 then (0x3ceac + D_2c4) else if cid =? 2 then (0x3d03c + D_2c4) else 0;
pc_asan_memcpy := (0x51db0 + D_2c4);   pc_asan_memset := (0x5224c + D_2c4);
pc_wrap_memcpy := (0x51dac + D_2c4);   pc_wrap_memset := (0x51da8 + D_2c4);   pc_wrap_memcmp := (0x420d4 + D_2c4);  pc_wrap_bcmp := (0x420d8 + D_2c4);
pc_wrap_read := (0x420e4 + D_2c4);     pc_wrap_fwrite := (0x420e8 + D_2c4);   pc_wrap_vprintf := (0x420f4 + D_2c4); pc_wrap_vfprintf := (0x420f8 + D_2c4);
pc_wrap_fprintf := (0x42100 + D_2c4);  pc_wrap_memchr := (0x420dc + D_2c4);   pc_wrap_strnlen := (0x420c8 + D_2c4);
pc_region_is_poisoned := (0x54c74 + D_2c4);
pc_spin_mmapdie := (0x60500 + D_2c4);  pc_spin_batch := (0x35f68 + D_150);    pc_spin_freearray := (0x34944 + D_150); pc_spin_shadow := (0x6ea08 + D_2c4)
|}.
Definition TFX_INST : Z := (0xa6b58 + D_10c0).
Definition TFX_TP : Z := (0x5dd150 + D_10c0).
Definition TFX_TSD : Z := (0x5fe4f8 + D_10c0).
Definition TFX_DEPOT : Z := (0x18c098 + D_10c0).
Definition TFX_STORE : Z := (0x17c088 + D_10c0).
Definition TFX_IAL_LO : Z := (0xab3c0 + D_10c0).
Definition TFX_IAL_HI : Z := (0x12c3f0 + D_10c0).
Definition TFX_IAL_W : Z := (0xec180 + D_10c0).
Definition TFX_IAL_FLAG : Z := (0x139c48 + D_10c0).
Definition TFX_OOM : Z := (0x12c420 + D_10c0).
Definition TFX_MAIN : Z := (0x80b0c + D_2c4).
Definition TFX_MAIN_RA : Z := (0x91100 + D_104c).
Definition TFX_GP : Z := 0x10800.
Definition TFX_ERRNO : Z := (0x5dd0ac + D_10c0).
Definition DRV_TRACES : list (list Z) :=
[[(0x533a4 + D_2c4); (0x80b60 + D_2c4)]; [(0x533a4 + D_2c4); (0x80bb4 + D_2c4)]; [(0x533a4 + D_2c4); (0x80e40 + D_2c4)]; [(0x533a4 + D_2c4)];
[(0x53244 + D_2c4); (0x80bd8 + D_2c4)]; [(0x53244 + D_2c4); (0x80d08 + D_2c4)]; [(0x53244 + D_2c4); (0x80ed4 + D_2c4)]; [(0x53244 + D_2c4)]].
Definition Tfx_const_sym : list acell :=
[ c8 (AT 0) (AC 0); c8 (AT 8) (ATop 0); c8 (AT 16) (ATop (- kStackSpan)); z8 (AT 24) 0; z8 (AT 32) 0; z1 (AT 40) 0;
z8 (AT 48) (0x5dd888 + D_10c0); z8 (AT 56) (0x5dd964 + D_10c0); z8 (AT 64) (0x5dd158 + D_10c0); c8 (AT 72) (AF 0)   ;
z4 (AC 8) 0; c8 (AC 152) (AT 0);
c8 (ATsd 0) (AC 0); c8 (ATp 0) (AF 0); c8 (ATp (-88)) (ATsd 0); z8 (ATp (-8)) (0x5dd170 + D_10c0) ;
c8 (ATp 8) (AD 0); c8 (AD 24) (ATp 0) ;
c8 (AInst o_space) (ASp 0); c8 (AInst o_rinfo) (ASp kRegionInfoOff); c8 (AInst o_sec_chunks) (AQ 0); c8 (AInst 80) (AQ 0) ].
Definition Tfx_const_abs : list acell :=
[
z8 (ANum (0x13bce8 + D_10c0)) 0x1 ;
z8 (ANum (0x13bcf0 + D_10c0)) 0x0 ;
z8 (ANum (0x13bcf8 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd00 + D_10c0)) (0x13f47 + D_20) ;
z8 (ANum (0x13bd08 + D_10c0)) 0x1e00010000 ;
z8 (ANum (0x13bd10 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd18 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd20 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd28 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd30 + D_10c0)) 0x10101000101 ;
z8 (ANum (0x13bd38 + D_10c0)) 0x100000000 ;
z8 (ANum (0x13bd40 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd48 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd50 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd58 + D_10c0)) 0x10001 ;
z8 (ANum (0x13bd60 + D_10c0)) 18446744073709551615 ;
z8 (ANum (0x13bd68 + D_10c0)) (0x11836 + D_20) ;
z8 (ANum (0x13bd70 + D_10c0)) 0x100 ;
z8 (ANum (0x13bd78 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd80 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd88 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd90 + D_10c0)) 0x0 ;
z8 (ANum (0x13bd98 + D_10c0)) 0xffffffff00000000 ;
z8 (ANum (0x13bda0 + D_10c0)) 0x1 ;
z8 (ANum (0x13bda8 + D_10c0)) (0x142b9 + D_20) ;
z8 (ANum (0x13bdb0 + D_10c0)) (0x13f47 + D_20) ;
z8 (ANum (0x13bdb8 + D_10c0)) (0x13f47 + D_20) ;
z8 (ANum (0x13bdc0 + D_10c0)) 0x10101000100 ;
z8 (ANum (0x13bdc8 + D_10c0)) 0x0 ;
z8 (ANum (0x13bdd0 + D_10c0)) (0x1db25 + D_m9) ;
z8 (ANum (0x13bdd8 + D_10c0)) 0x101000100000000 ;
z8 (ANum (0x13bde0 + D_10c0)) 0x101010101010101 ;
z8 (ANum (0x13bde8 + D_10c0)) 0x1010101 ;
z8 (ANum (0x13bdf0 + D_10c0)) 0x10100000001 ;
z8 (ANum (0xa79b8 + D_10c0)) 0x100ffffffff ;
z8 (ANum (0xa79c0 + D_10c0)) 0x1000000400 ;
z8 (ANum (0xa79c8 + D_10c0)) 0x800 ;
z8 (ANum (0xa79d0 + D_10c0)) 0x101010000000001 ;
z8 (ANum (0xa79d8 + D_10c0)) 0x1400000010 ;
z8 (ANum (0xa79e0 + D_10c0)) 0x100000000000 ;
z8 (ANum (0xa79e8 + D_10c0)) 0xbe00000000 ;
z8 (ANum (0xa79f0 + D_10c0)) 0x100000055 ;
z8 (ANum (0xa79f8 + D_10c0)) 0x0 ;
z8 (ANum (0xa7a00 + D_10c0)) 0x1000100000000 ;
z8 (ANum (0xa7a08 + D_10c0)) 0x101010101000001 ;
z8 (ANum (0xa7a10 + D_10c0)) 0x1 ;
z8 (ANum (0xa7a18 + D_10c0)) 0x200000001 ;
z8 (ANum (0xa7a20 + D_10c0)) (0x13f47 + D_20) ;
z8 (ANum (0xa7a28 + D_10c0)) 0x10101 ;
z8 (ANum (0xaa1b8 + D_10c0)) 0x7fff8000 ;
z4 (ANum (0xaa1c0 + D_10c0)) 0x1 ;
z1 (ANum (0xaae98 + D_10c0)) 0x1 ;
z1 (ANum (0xaae99 + D_10c0)) 0x1 ;
z8 (ANum (0xaaea0 + D_10c0)) 0x7fffffffffff ;
z8 (ANum (0xaaea8 + D_10c0)) 0x0 ;
z8 (ANum (0xaaeb0 + D_10c0)) 0x0 ;
z4 (ANum (0xaaebc + D_10c0)) 0x1e ;
z1 (ANum (0xa9a1c + D_10c0)) 0x1 ;
z1 (ANum (0xa9a20 + D_10c0)) 0x1 ;
z4 (ANum (0xa9a24 + D_10c0)) 0x0 ;
z1 (ANum (0x12c421 + D_10c0)) 0x1 ;
z1 (ANum (0x12c422 + D_10c0)) 0x0 ;
z8 (ANum (0x139c60 + D_10c0)) 0x1000 ;
z4 (ANum (0x13bcdc + D_10c0)) 0x0 ;
z8 (ANum (0xa3ff0 + D_10f0)) (0x9b0d4 + D_10ec) ;
z8 (ANum (0xa3ff8 + D_10f0)) (0x9b490 + D_10ec) ;
z8 (ANum (0xa4000 + D_10f0)) (0x9b894 + D_10ec) ;
z8 (ANum (0xa3ea0 + D_10f0)) (0x9b460 + D_10ec) ;
z8 (ANum (0xa3ea8 + D_10f0)) (0x9b390 + D_10ec) ;
z1 (ANum (0x13bd71 + D_10c0)) 0x1 ;
z4 (ANum (0x139c58 + D_10c0)) 0x0 ;
z8 (ANum (0xa2e78 + D_10f0)) 0x8 ;
z8 (ANum (0xa3ec0 + D_10f0)) (0xa0b94 + D_10ec) ;
z8 (ANum (0xa3ec8 + D_10f0)) (0x97a04 + D_10ec) ;
z8 (ANum (0xa3fa8 + D_10f0)) (0x9bd1c + D_10ec) ;
z8 (ANum (0xa3eb0 + D_10f0)) (0x9b394 + D_10ec) ;
z1 (ANum (0x13bde3 + D_10c0)) 0x1 ;
z1 (ANum (0x13bd3c + D_10c0)) 0x1 ;
z8 (ANum (0xa3ee0 + D_10f0)) (0x9addc + D_10ec) ;
z8 (ANum (0xa3ee8 + D_10f0)) (0x97ccc + D_10ec) ;
z8 (ANum (0xa3f28 + D_10f0)) (0x9c084 + D_10ec) ;
z8 (ANum (0xa2cc8 + D_10f0)) (0xaae99 + D_10c0) ;
z8 (ANum (0xa2e00 + D_10f0)) (0xa6a50 + D_10f0) ;
z8 (ANum (0xa2e08 + D_10f0)) (0xa6ad0 + D_10f0) ;
z8 (ANum (0xa6b00 + D_10c0)) 0x1 ;
z8 (ANum (0xa2e68 + D_10f0)) 0x1 ;
z8 (ANum (0xa2e70 + D_10f0)) 0xfffffffffffff800 ;
z8 (ANum (0x17c090 + D_10c0)) 0x800000 ;
z8 (ANum (0xa6b60 + D_10c0)) 0x2000011000 ;
z8 (ANum (0xa6b68 + D_10c0)) (0x16bbb + D_20) ;
z8 (ANum (0xa6b70 + D_10c0)) 0x0 ;
z8 (ANum (0xa6b80 + D_10c0)) 0xffffffff ;
z8 (ANum (0xa6b90 + D_10c0)) 0x0 ;
z8 (ANum (0xa6b98 + D_10c0)) 0x1000 ;
z8 (ANum (0xa6bb0 + D_10c0)) 0x800000 ;
z8 (ANum (0xa6bb8 + D_10c0)) (0x192b8 + D_20) ;
z8 (ANum (0xa6bc0 + D_10c0)) 0x0 ;
z8 (ANum (0xa6e70 + D_10c0)) 0x10000000 ;
z8 (ANum (0xa6e78 + D_10c0)) 0xe666661 ;
z8 (ANum (0xa6e80 + D_10c0)) 0x100000 ;
z8 (ANum (0xa7978 + D_10c0)) 0x10000000000 ;
z8 (ANum (0xa7980 + D_10c0)) 0x108000010 ;
z8 (ANum (0x5dd0f8 + D_10c0)) (0x5fe4f8 + D_10c0) ;
z8 (ANum (0x5dd148 + D_10c0)) (0x5dd170 + D_10c0) ;
z8 (ANum (0x5dd170 + D_10c0)) 0x1 ;
z8 (ANum (0x5dd178 + D_10c0)) (0x5dd950 + D_10c0) ;
z8 (ANum (0x5dd160 + D_10c0)) 0x0 ;
z8 (ANum (0x103c0 + D_20)) 0x218a392cd3d5dbf ;
z8 (ANum (0x10328 + D_10)) 0xcc6e96b9cc6e96b9 ;
z8 (ANum (0x103a8 + D_20)) 0xafffff00000fffff ;
z8 (ANum 0x102e8) 0xc6a4a7935bd1e995 ;
z8 (ANum (0x10308 + D_8)) 0x35253c9ade8f4ca8 ;
z8 (ANum (0x103a0 + D_20)) 0x9747b28c9747b28c ;
z8 (ANum (0xa2db8 + D_10f0)) 0x10 ;
z8 (ANum (0x10530 + D_20)) 0x13080d0307020100 ;
z8 (ANum (0x10538 + D_20)) 0x281422091c0e1904 ;
z8 (ANum (0x10540 + D_20)) 0x301d2e0f261a1105 ;
z8 (ANum (0x10548 + D_20)) 0x3929321536231f0a ;
z8 (ANum (0x10550 + D_20)) 0x27211b18120c063f ;
z8 (ANum (0x10558 + D_20)) 0x3831351e2f2d2510 ;
z8 (ANum (0x10560 + D_20)) 0x37342c2420170b3e ;
z8 (ANum (0x10568 + D_20)) 0x3a3b2a3c332b163d ;
z8 (ANum (0x10430 + D_20)) 0x13080d0307020100 ;
z8 (ANum (0x10438 + D_20)) 0x281422091c0e1904 ;
z8 (ANum (0x10440 + D_20)) 0x301d2e0f261a1105 ;
z8 (ANum (0x10448 + D_20)) 0x3929321536231f0a ;
z8 (ANum (0x10450 + D_20)) 0x27211b18120c063f ;
z8 (ANum (0x10458 + D_20)) 0x3831351e2f2d2510 ;
z8 (ANum (0x10460 + D_20)) 0x37342c2420170b3e ;
z8 (ANum (0x10468 + D_20)) 0x3a3b2a3c332b163d ;
z8 (ANum (0x13bc80 + D_10c0)) 0x0 ;
z8 (ANum (0x13bc88 + D_10c0)) 0x0 ;
z8 (ANum (0x13bc90 + D_10c0)) 0x0 ;
z8 (ANum (0x13bc98 + D_10c0)) 0x0 ;
z8 (ANum (0x13bca0 + D_10c0)) 0x0 ;
z8 (ANum (0x13bca8 + D_10c0)) 0x0 ;
z8 (ANum (0x13bcb0 + D_10c0)) 0x0 ;
z8 (ANum (0x13bcb8 + D_10c0)) 0x0 ;
z8 (ANum (0x13bcc0 + D_10c0)) 0x0 ;
z8 (ANum (0x13bcc8 + D_10c0)) 0x0 ;
z8 (ANum (0xa2140 + D_10f0)) (0x139c60 + D_10c0) ;
z8 (ANum (0xa2148 + D_10f0)) (0xa4038 + D_10f0) ;
z8 (ANum (0xa2150 + D_10f0)) (0x13bce8 + D_10c0) ;
z8 (ANum (0xa2158 + D_10f0)) (0xa79b8 + D_10c0) ;
z8 (ANum (0xa2160 + D_10f0)) (0xaa1b8 + D_10c0) ;
z8 (ANum (0xa2168 + D_10f0)) (0xaaea8 + D_10c0) ;
z8 (ANum (0xa2170 + D_10f0)) (0xaaeb0 + D_10c0) ;
z8 (ANum (0xa2178 + D_10f0)) (0xaaea0 + D_10c0) ;
z8 (ANum (0xa2180 + D_10f0)) (0xa4000 + D_10f0) ;
z8 (ANum (0xa2188 + D_10f0)) (0xa3ff8 + D_10f0) ;
z8 (ANum (0xa2190 + D_10f0)) (0xa4030 + D_10f0) ;
z8 (ANum (0xa2198 + D_10f0)) (0xa4048 + D_10f0) ;
z8 (ANum (0xa21a0 + D_10f0)) 0x1 ;
z8 (ANum (0xa21a8 + D_10f0)) (0x13bcdc + D_10c0) ;
z8 (ANum (0xa21b0 + D_10f0)) (0x139c58 + D_10c0) ;
z8 (ANum (0xa21b8 + D_10f0)) (0xaa1c0 + D_10c0) ;
z8 (ANum (0xa6a50 + D_10f0)) 0x20ec0 ;
z8 (ANum (0xa6a58 + D_10f0)) 0x3 ;
z8 (ANum (0xa6a60 + D_10f0)) 0x20 ;
z8 (ANum (0xa6a68 + D_10f0)) (0x1c0ff + D_m9) ;
z8 (ANum (0xa6a70 + D_10f0)) 0x20ee0 ;
z8 (ANum (0xa6a78 + D_10f0)) 0x0 ;
z8 (ANum (0xa6a80 + D_10f0)) 0x0 ;
z8 (ANum (0xa6a88 + D_10f0)) 0xffffffffffffffff ;
z8 (ANum (0xa6a90 + D_10f0)) 0x20f00 ;
z8 (ANum (0xa6a98 + D_10f0)) 0x2 ;
z8 (ANum (0xa6aa0 + D_10f0)) 0x20 ;
z8 (ANum (0xa6aa8 + D_10f0)) (0x1c0ff + D_m9) ;
z8 (ANum (0xa6ab0 + D_10f0)) 0x20f20 ;
z8 (ANum (0xa6ab8 + D_10f0)) 0x0 ;
z8 (ANum (0xa6ac0 + D_10f0)) 0x0 ;
z8 (ANum (0xa6ac8 + D_10f0)) 0xffffffffffffffff ;
z1 (ANum (0x13c060 + D_10c0)) 0x0 ;
z8 (ANum (0xa7a70 + D_10c0)) 0x0 ;
z2 (ANum (0xa6eca + D_10c0)) 0x0 ;
z4 (ANum (0xa6ecc + D_10c0)) 0x0 ;
z1 (ANum (0xa6e01 + D_10c0)) 0x0 ;
z2 (ANum (0xa6e02 + D_10c0)) 0x0 ;
z4 (ANum (0xa6e04 + D_10c0)) 0x0 ;
z8 (ANum (0xa4038 + D_10f0)) (0x192b8 + D_20)  ;
z8 (ANum (0x1cdaf + D_m9)) 0x612079726f6d656d ;
z8 (ANum (0x1cdb7 + D_m9)) 0x7365726464612074 ;
z4 (ANum (0x1cdbf + D_m9)) 0x70252073 ;
z1 (ANum (0x1cdc3 + D_m9)) 0x0 ;
z4 (ANum (0x20c3c + D_m8)) (0x469b0 + D_2cc) ;
z8 (ANum (0xa2e10 + D_10f0)) (0x5fd190 + D_10c0) ;
z8 (ANum (0x5fd410 + D_10c0)) 0x1000 ;
z1 (ANum 0x2150c) 0x04 ;
z1 (ANum 0x2150d) 0xff ;
z4 (ANum 0x214a8) (0x6f924 + D_104c) ;
z1 (ANum (0x13bdc3 + D_10c0)) 0x1 ;
z1 (ANum (0x13bddc + D_10c0)) 0x1
].
Definition Tfx_const_shadow : list acell :=
[ z1 (ANum 0x7fffc1d8) 0x3 ;
z1 (ANum 0x7fffc1d9) 0xf9 ;
z1 (ANum 0x7fffc1da) 0xf9 ;
z1 (ANum 0x7fffc1db) 0xf9 ;
z1 (ANum 0x7fffc1e0) 0x2 ;
z1 (ANum 0x7fffc1e1) 0xf9 ;
z1 (ANum 0x7fffc1e2) 0xf9 ;
z1 (ANum 0x7fffc1e3) 0xf9 ;
z1 (ANum (0x8000cd4a + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd4b + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd4c + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd4d + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd4e + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd4f + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd50 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd51 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd52 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd53 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd54 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd55 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd56 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd57 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd58 + D_21e)) 0xf9 ;
z1 (ANum (0x8000cd59 + D_21e)) 0xf9  ].
Definition Tfx_const (ly : alayout) : list acell := Tfx_const_sym ++ Tfx_const_abs ++ Tfx_const_shadow.
Definition Tfx_zero_shadow : list (Z * Z) :=
[ (0x10000, 0x20ec0 - 0x10000); (0x20ee0, 0x20); (0x20f20, (0xa6a50 + D_10f0) - 0x20f20); ((0xa6ad0 + D_10f0), (0x5ff000 + D_1000) - (0xa6ad0 + D_10f0)) ].
Definition Tfx_owned_static : list (Z * Z) :=
[ ((0xa3e80 + D_10f0), (0xa6708 + D_10f0) - (0xa3e80 + D_10f0)); ((0xa6a50 + D_10f0), 0x80); ((0xa6b00 + D_10c0), 8); ((0xa6b58 + D_10c0), (0x5cc810 + D_10c0) - (0xa6b58 + D_10c0)) ; ((0x5dd150 + D_10c0), 0x3c) ;
((0xa2160 + D_10f0), 8); ((0xa21b8 + D_10f0), 8);
(0x102e8, 8); ((0x10308 + D_8), 8); ((0x10328 + D_10), 8); ((0x103a0 + D_20), 8); ((0x103a8 + D_20), 8); ((0x103c0 + D_20), 8); ((0x10430 + D_20), 64); ((0x10530 + D_20), 64);
((0xa2140 + D_10f0), 0x20); ((0xa2168 + D_10f0), 0x18); ((0xa2180 + D_10f0), 0x38); ((0xa2cc8 + D_10f0), 8); ((0xa2db8 + D_10f0), 8); ((0xa2e00 + D_10f0), 16); ((0xa2e68 + D_10f0), 16); ((0xa2e78 + D_10f0), 8) ;
(0x20ec0, 0x20); (0x20f00, 0x20);
((0x5dd0f8 + D_10c0), 8); ((0x5dd148 + D_10c0), 8); ((0x5dd160 + D_10c0), 8) ; ((0x5fe4f8 + D_10c0), 8);
((0x1cdaf + D_m9), 21); ((0x20c3c + D_m8), 4); (0x214a8, 4); (0x2150c, 2); ((0xa2e10 + D_10f0), 8); ((0x5fd410 + D_10c0), 8) ].
Definition TFX_TR0 (h : nat) : list Z := match h with O => [(0x3ece8 + D_2c4); (0x40038 + D_2c4)] | _ => [(0x3ece8 + D_2c4)] end.
Definition TFX_HASH (h : nat) : Z := match h with O => (17781918613732324073 + D_mcf6373b41df84414) | _ => (7684849787024974657 + D_m5c6cf5c3c23d561f) end.
Definition TfxSyms (B : asyms) : Prop := match imgk with K_tra => YF90.TraSyms B | K_trb => YF9j.TrbSyms B end.
End i.
Notation TSEGS := tfxsegs (only parsing).
Definition img_e2 (k : img) : Z := match k with K_trb => 1 | _ => 0 end.
Lemma P_facts (k : img) :
0 <= img_e2 k <= 1
/\ @D_m8 k = (-8) * img_e2 k
/\ @D_8 k = 0x8 * img_e2 k
/\ @D_m9 k = (-9) * img_e2 k
/\ @D_10 k = 0x10 * img_e2 k
/\ @D_18 k = 0x18 * img_e2 k
/\ @D_20 k = 0x20 * img_e2 k
/\ @D_30 k = 0x30 * img_e2 k
/\ @D_m3c k = (-60) * img_e2 k
/\ @D_m3e k = (-62) * img_e2 k
/\ @D_m40 k = (-64) * img_e2 k
/\ @D_4e k = 0x4e * img_e2 k
/\ @D_50 k = 0x50 * img_e2 k
/\ @D_6c k = 0x6c * img_e2 k
/\ @D_a0 k = 0xa0 * img_e2 k
/\ @D_150 k = 0x150 * img_e2 k
/\ @D_200 k = 0x200 * img_e2 k
/\ @D_218 k = 0x218 * img_e2 k
/\ @D_21c k = 0x21c * img_e2 k
/\ @D_21e k = 0x21e * img_e2 k
/\ @D_220 k = 0x220 * img_e2 k
/\ @D_270 k = 0x270 * img_e2 k
/\ @D_274 k = 0x274 * img_e2 k
/\ @D_280 k = 0x280 * img_e2 k
/\ @D_2b4 k = 0x2b4 * img_e2 k
/\ @D_2c4 k = 0x2c4 * img_e2 k
/\ @D_2cc k = 0x2cc * img_e2 k
/\ @D_m3ac k = (-940) * img_e2 k
/\ @D_430 k = 0x430 * img_e2 k
/\ @D_440 k = 0x440 * img_e2 k
/\ @D_a2c k = 0xa2c * img_e2 k
/\ @D_1000 k = 0x1000 * img_e2 k
/\ @D_104c k = 0x104c * img_e2 k
/\ @D_10c0 k = 0x10c0 * img_e2 k
/\ @D_10e0 k = 0x10e0 * img_e2 k
/\ @D_10e8 k = 0x10e8 * img_e2 k
/\ @D_10ec k = 0x10ec * img_e2 k
/\ @D_10f0 k = 0x10f0 * img_e2 k
/\ @D_1100 k = 0x1100 * img_e2 k
/\ @D_54c0 k = 0x54c0 * img_e2 k
/\ @D_5680 k = 0x5680 * img_e2 k
/\ @D_m27b919177701d40 k = (-178896664171388224) * img_e2 k
/\ @D_m10c55b69b38ab717 k = (-1208472584560752407) * img_e2 k
/\ @D_m261b33dfb1afee1d k = (-2745845433664269853) * img_e2 k
/\ @D_332fe4d8b3da5a5b k = 0x332fe4d8b3da5a5b * img_e2 k
/\ @D_558ab28b2f16c771 k = 0x558ab28b2f16c771 * img_e2 k
/\ @D_m5c6cf5c3c23d561f k = (-6659968170100348447) * img_e2 k
/\ @D_ma7775317fd2cb971 k = (-12067205089059453297) * img_e2 k
/\ @D_mcf6373b41df84414 k = (-14943915205979554836) * img_e2 k
/\ @tfxguard_start k = 0x80f34 + 0x2c4 * img_e2 k
/\ @tfxmusl_text_start k = 0x90bb8 + 0x104c * img_e2 k
/\ @tfx_A_musl_memchr k = 0x9b394 + 0x10ec * img_e2 k
/\ @tfx_A_musl_memcmp k = 0x9b460 + 0x10ec * img_e2 k
/\ @tfx_A_musl_memcpy k = 0x9b490 + 0x10ec * img_e2 k
/\ @tfx_A_musl_memset k = 0x9b894 + 0x10ec * img_e2 k
/\ @tfx_A_musl_strnlen k = 0x9bd1c + 0x10ec * img_e2 k
/\ @TFX_DEPOT k = 0x18c098 + 0x10c0 * img_e2 k
/\ @TFX_ERRNO k = 0x5dd0ac + 0x10c0 * img_e2 k
/\ @TFX_IAL_FLAG k = 0x139c48 + 0x10c0 * img_e2 k
/\ @TFX_IAL_HI k = 0x12c3f0 + 0x10c0 * img_e2 k
/\ @TFX_IAL_LO k = 0xab3c0 + 0x10c0 * img_e2 k
/\ @TFX_IAL_W k = 0xec180 + 0x10c0 * img_e2 k
/\ @TFX_INST k = 0xa6b58 + 0x10c0 * img_e2 k
/\ @TFX_MAIN k = 0x80b0c + 0x2c4 * img_e2 k
/\ @TFX_MAIN_RA k = 0x91100 + 0x104c * img_e2 k
/\ @TFX_OOM k = 0x12c420 + 0x10c0 * img_e2 k
/\ @TFX_STORE k = 0x17c088 + 0x10c0 * img_e2 k
/\ @TFX_TP k = 0x5dd150 + 0x10c0 * img_e2 k
/\ @TFX_TSD k = 0x5fe4f8 + 0x10c0 * img_e2 k
.
Proof. destruct k; cbv; repeat split; congruence. Qed.
Ltac img_occurs k :=
lazymatch goal with
| |- context [k] => constr:(true)
| _ => match goal with
| x := ?b |- ?G => lazymatch b with context [k] => lazymatch G with context [x] => constr:(true) end end
| _ => constr:(false)
end
end.
Ltac img_clear_sel k :=
repeat match goal with
| H : ?T |- _ => lazymatch T with context [k] => clear H end
| H := ?b |- _ => lazymatch b with context [k] => clear H end
end.
Ltac img_clear k := first [ clear - k | img_clear_sel k ].
Ltac img_is_arith T :=
lazymatch T with
| @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq N _ _ => idtac
| @eq bool _ _ => idtac
| Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
| le _ _ => idtac | lt _ _ => idtac | ge _ _ => idtac | gt _ _ => idtac
| ?A /\ ?B => first [img_is_arith A | img_is_arith B]
| ?A \/ ?B => first [img_is_arith A | img_is_arith B]
| ~ ?A => img_is_arith A
| ?A -> ?B => first [img_is_arith A | img_is_arith B]
end.
Ltac img_clear_na k :=
repeat match goal with
| H : ?T |- _ => lazymatch T with context [k] => tryif img_is_arith T then fail else clear H end
| H := ?b |- _ => lazymatch b with context [k] => clear H end
end.
Ltac img_subst_lets k :=
repeat match goal with x := ?b |- ?G => lazymatch b with context [k] => lazymatch G with context [x] => subst x end end end.
Ltac img_gen_destruct k := img_subst_lets k; let k' := fresh "imgk_c" in generalize k; intro k'; destruct k'.
Ltac img_revert_arith k :=
repeat match goal with H : ?T |- _ => lazymatch T with context [k] => tryif img_is_arith T then revert H else fail end end.
Ltac img_case :=
lazymatch goal with
| k := _ : img |- _ => idtac
| k : img |- _ => let b := img_occurs k in
lazymatch b with
| true => first [ img_gen_destruct k | (img_clear k; destruct k) ]
| false => idtac end
| _ => idtac
end.
Ltac img_unfold_all := unfold D_m8, D_8, D_m9, D_10, D_18, D_20, D_30, D_m3c, D_m3e, D_m40, D_4e, D_50, D_6c, D_a0, D_150, D_200, D_218, D_21c, D_21e, D_220, D_270, D_274, D_280, D_2b4, D_2c4, D_2cc, D_m3ac, D_430, D_440, D_a2c, D_1000, D_104c, D_10c0, D_10e0, D_10e8, D_10ec, D_10f0, D_1100, D_54c0, D_5680, D_m27b919177701d40, D_m10c55b69b38ab717, D_m261b33dfb1afee1d, D_332fe4d8b3da5a5b, D_558ab28b2f16c771, D_m5c6cf5c3c23d561f, D_ma7775317fd2cb971, D_mcf6373b41df84414, tfxguard_start, tfxmusl_text_start, tfx_A_musl_memchr, tfx_A_musl_memcmp, tfx_A_musl_memcpy, tfx_A_musl_memset, tfx_A_musl_strnlen, TFX_DEPOT, TFX_ERRNO, TFX_GP, TFX_IAL_FLAG, TFX_IAL_HI, TFX_IAL_LO, TFX_IAL_W, TFX_INST, TFX_MAIN, TFX_MAIN_RA, TFX_OOM, TFX_STORE, TFX_TP, TFX_TSD in *.
Ltac img_concrete :=
repeat match goal with k := _ : img |- _ => subst k end;
try (lazymatch goal with k : img |- _ => first [ (img_revert_arith k; img_gen_destruct k; intros) | (img_clear_na k; destruct k) ] end).
Ltac img_inst1 :=
lazymatch goal with |- ?G => has_evar G end;
match goal with k : img |- context [?e] => is_evar e; let T := type of e in lazymatch T with img => unify e k end end.
Ltac img_inst := img_inst1; repeat img_inst1.
Ltac img_arith_rel :=
lazymatch goal with
| k : img |- _ => first [ lazymatch goal with |- context [k] => idtac end
| match goal with H : ?T |- _ => lazymatch T with context [k] => img_is_arith T end end ]
end.
Ltac img_facts := lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_has_moddiv := lazymatch goal with |- context [Z.modulo _ _] => idtac | |- context [Z.div _ _] => idtac end.
Ltac img_local := lazymatch goal with k := _ : img |- _ => idtac end.
Ltac img_local_unfold := repeat match goal with k := _ : img |- _ => progress (unfold k in * ) end.
Ltac img_has_match :=
lazymatch goal with
| k : img |- _ =>
lazymatch goal with
| |- context [match k with K_tra => _ | K_trb => _ end] => idtac
| _ : context [match k with K_tra => _ | K_trb => _ end] |- _ => idtac
end
end.
Ltac img_goal_has_k := lazymatch goal with k := _ : img |- _ => fail | k : img |- ?G => lazymatch G with context [k] => idtac end end.
Ltac img_lia :=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Ltac img_refl := first [ timeout 120 reflexivity | (img_case; reflexivity) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Tactic Notation "img_exact" uconstr(t) :=
first [ timeout 120 (exact t)   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
| (let H := fresh "IMGX" in pose proof t as H; revert H; img_case; intro H; exact H)
| (img_case; exact t)
| (lazymatch goal with k : img |- _ => img_clear_na k; destruct k end; exact t)
| (lazymatch goal with k : img |- _ => destruct k end; exact t) ].
Ltac img_raw := lazymatch goal with k := _ : img |- _ => fail | k : img |- _ => first [ destruct k | (img_revert_arith k; img_gen_destruct k; intros) ] end; img_unfold_all.
Tactic Notation "img_try" tactic3(t) :=
first [ t | (img_inst; t)
| (try img_inst; first [ (img_local; img_local_unfold; img_unfold_all; t) | (img_case; img_unfold_all; t) | (img_raw; t) ]) ].
Ltac img_eq_by_case := first [ timeout 60 reflexivity | (img_case; reflexivity) | (img_case; vm_compute; reflexivity) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Tactic Notation "img_change" uconstr(a) "with" uconstr(b) :=
first [ timeout 60 (change a with b) | (let a' := constr:(a) in let b' := constr:(b) in first [ timeout 60 (change a' with b') | replace a' with b' by img_eq_by_case ]) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Tactic Notation "img_change" uconstr(a) "with" uconstr(b) "in" hyp(H) :=
first [ timeout 60 (change a with b in H) | (let a' := constr:(a) in let b' := constr:(b) in first [ timeout 60 (change a' with b' in H) | replace a' with b' in H by img_eq_by_case ]) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Tactic Notation "img_change" uconstr(a) "with" uconstr(b) "in" "*" :=
first [ timeout 60 (change a with b in * ) | (let a' := constr:(a) in let b' := constr:(b) in first [ timeout 60 (change a' with b' in * ) | replace a' with b' in * by img_eq_by_case ]) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Ltac img_concl T := lazymatch T with | ?A -> ?B => img_concl B | ?C => C end.
Ltac img_solve_inst := lazymatch goal with |- img => first [ eassumption | exact _ ] | _ => idtac end.
Tactic Notation "img_apply" uconstr(t) :=
first [ timeout 120 (apply t); img_solve_inst   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
| (let H := fresh "IMGA" in pose proof t as H;
let C := img_concl ltac:(type of H) in
cut C; [ clear H; let HC := fresh "IMGC" in intro HC; revert HC; img_case; intro HC; exact HC | apply H ])
| solve [ img_case; apply t ] ].
Ltac img_destruct k :=
destruct k; [ set (imgk_ := K_tra) in * | set (imgk_ := K_trb) in * ].
Ltac img_eqrefl := first [ timeout 60 (exact eq_refl) | (try img_inst; img_case; vm_compute; reflexivity) | (try img_inst; img_case; reflexivity) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
Ltac img_dfacts :=
lazymatch goal with
| k := ?c : img |- _ => (let v := eval vm_compute in (@D_m8 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m8 k = v) by reflexivity; assert (H2 : @D_m8 c = v) by reflexivity); (let v := eval vm_compute in (@D_8 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_8 k = v) by reflexivity; assert (H2 : @D_8 c = v) by reflexivity); (let v := eval vm_compute in (@D_m9 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m9 k = v) by reflexivity; assert (H2 : @D_m9 c = v) by reflexivity); (let v := eval vm_compute in (@D_10 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10 k = v) by reflexivity; assert (H2 : @D_10 c = v) by reflexivity); (let v := eval vm_compute in (@D_18 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_18 k = v) by reflexivity; assert (H2 : @D_18 c = v) by reflexivity); (let v := eval vm_compute in (@D_20 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_20 k = v) by reflexivity; assert (H2 : @D_20 c = v) by reflexivity); (let v := eval vm_compute in (@D_30 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_30 k = v) by reflexivity; assert (H2 : @D_30 c = v) by reflexivity); (let v := eval vm_compute in (@D_m3c k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m3c k = v) by reflexivity; assert (H2 : @D_m3c c = v) by reflexivity); (let v := eval vm_compute in (@D_m3e k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m3e k = v) by reflexivity; assert (H2 : @D_m3e c = v) by reflexivity); (let v := eval vm_compute in (@D_m40 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m40 k = v) by reflexivity; assert (H2 : @D_m40 c = v) by reflexivity); (let v := eval vm_compute in (@D_4e k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_4e k = v) by reflexivity; assert (H2 : @D_4e c = v) by reflexivity); (let v := eval vm_compute in (@D_50 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_50 k = v) by reflexivity; assert (H2 : @D_50 c = v) by reflexivity); (let v := eval vm_compute in (@D_6c k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_6c k = v) by reflexivity; assert (H2 : @D_6c c = v) by reflexivity); (let v := eval vm_compute in (@D_a0 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_a0 k = v) by reflexivity; assert (H2 : @D_a0 c = v) by reflexivity); (let v := eval vm_compute in (@D_150 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_150 k = v) by reflexivity; assert (H2 : @D_150 c = v) by reflexivity); (let v := eval vm_compute in (@D_200 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_200 k = v) by reflexivity; assert (H2 : @D_200 c = v) by reflexivity); (let v := eval vm_compute in (@D_218 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_218 k = v) by reflexivity; assert (H2 : @D_218 c = v) by reflexivity); (let v := eval vm_compute in (@D_21c k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_21c k = v) by reflexivity; assert (H2 : @D_21c c = v) by reflexivity); (let v := eval vm_compute in (@D_21e k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_21e k = v) by reflexivity; assert (H2 : @D_21e c = v) by reflexivity); (let v := eval vm_compute in (@D_220 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_220 k = v) by reflexivity; assert (H2 : @D_220 c = v) by reflexivity); (let v := eval vm_compute in (@D_270 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_270 k = v) by reflexivity; assert (H2 : @D_270 c = v) by reflexivity); (let v := eval vm_compute in (@D_274 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_274 k = v) by reflexivity; assert (H2 : @D_274 c = v) by reflexivity); (let v := eval vm_compute in (@D_280 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_280 k = v) by reflexivity; assert (H2 : @D_280 c = v) by reflexivity); (let v := eval vm_compute in (@D_2b4 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_2b4 k = v) by reflexivity; assert (H2 : @D_2b4 c = v) by reflexivity); (let v := eval vm_compute in (@D_2c4 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_2c4 k = v) by reflexivity; assert (H2 : @D_2c4 c = v) by reflexivity); (let v := eval vm_compute in (@D_2cc k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_2cc k = v) by reflexivity; assert (H2 : @D_2cc c = v) by reflexivity); (let v := eval vm_compute in (@D_m3ac k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m3ac k = v) by reflexivity; assert (H2 : @D_m3ac c = v) by reflexivity); (let v := eval vm_compute in (@D_430 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_430 k = v) by reflexivity; assert (H2 : @D_430 c = v) by reflexivity); (let v := eval vm_compute in (@D_440 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_440 k = v) by reflexivity; assert (H2 : @D_440 c = v) by reflexivity); (let v := eval vm_compute in (@D_a2c k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_a2c k = v) by reflexivity; assert (H2 : @D_a2c c = v) by reflexivity); (let v := eval vm_compute in (@D_1000 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_1000 k = v) by reflexivity; assert (H2 : @D_1000 c = v) by reflexivity); (let v := eval vm_compute in (@D_104c k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_104c k = v) by reflexivity; assert (H2 : @D_104c c = v) by reflexivity); (let v := eval vm_compute in (@D_10c0 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10c0 k = v) by reflexivity; assert (H2 : @D_10c0 c = v) by reflexivity); (let v := eval vm_compute in (@D_10e0 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10e0 k = v) by reflexivity; assert (H2 : @D_10e0 c = v) by reflexivity); (let v := eval vm_compute in (@D_10e8 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10e8 k = v) by reflexivity; assert (H2 : @D_10e8 c = v) by reflexivity); (let v := eval vm_compute in (@D_10ec k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10ec k = v) by reflexivity; assert (H2 : @D_10ec c = v) by reflexivity); (let v := eval vm_compute in (@D_10f0 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_10f0 k = v) by reflexivity; assert (H2 : @D_10f0 c = v) by reflexivity); (let v := eval vm_compute in (@D_1100 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_1100 k = v) by reflexivity; assert (H2 : @D_1100 c = v) by reflexivity); (let v := eval vm_compute in (@D_54c0 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_54c0 k = v) by reflexivity; assert (H2 : @D_54c0 c = v) by reflexivity); (let v := eval vm_compute in (@D_5680 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_5680 k = v) by reflexivity; assert (H2 : @D_5680 c = v) by reflexivity); (let v := eval vm_compute in (@D_m27b919177701d40 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m27b919177701d40 k = v) by reflexivity; assert (H2 : @D_m27b919177701d40 c = v) by reflexivity); (let v := eval vm_compute in (@D_m10c55b69b38ab717 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m10c55b69b38ab717 k = v) by reflexivity; assert (H2 : @D_m10c55b69b38ab717 c = v) by reflexivity); (let v := eval vm_compute in (@D_m261b33dfb1afee1d k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_m261b33dfb1afee1d k = v) by reflexivity; assert (H2 : @D_m261b33dfb1afee1d c = v) by reflexivity); (let v := eval vm_compute in (@D_332fe4d8b3da5a5b k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_332fe4d8b3da5a5b k = v) by reflexivity; assert (H2 : @D_332fe4d8b3da5a5b c = v) by reflexivity); (let v := eval vm_compute in (@D_558ab28b2f16c771 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_558ab28b2f16c771 k = v) by reflexivity; assert (H2 : @D_558ab28b2f16c771 c = v) by reflexivity); (let v := eval vm_compute in (@D_ma7775317fd2cb971 k) in let H := fresh "DF" in let H2 := fresh "DF" in assert (H : @D_ma7775317fd2cb971 k = v) by reflexivity; assert (H2 : @D_ma7775317fd2cb971 c = v) by reflexivity); idtac
| _ => idtac
end.
Ltac img_expose := cbv beta iota delta [tfxguard_count tfxguard_start tfxmusl_tbl tfxmusl_text_count tfxmusl_text_start tfxsegs tfxtbl_rtA tfxtbl_rtA_build tfxtbl_rtB tfxtbl_rtB_build tfxtbl_rtC tfxtbl_rtC_build tfxtbl_rtD tfxtbl_rtD_build tfxtbl_rtF tfxtbl_rtF_build tfxtbl_rtG tfxtbl_rtG_build tfxtbl_rtK tfxtbl_rtK_build tfxtbl_rtM tfxtbl_rtM_build tfx_A_musl_memchr tfx_A_musl_memcmp tfx_A_musl_memcpy tfx_A_musl_memset tfx_A_musl_strnlen Tfx_code DRV_TRACES TFX_DEPOT TFX_ERRNO TFX_GP TFX_HASH TFX_IAL_FLAG TFX_IAL_HI TFX_IAL_LO TFX_IAL_W TFX_INST TFX_MAIN TFX_MAIN_RA TFX_OOM TFX_STORE TFX_TP TFX_TR0 TFX_TSD Tfx_const Tfx_const_abs Tfx_const_shadow Tfx_const_sym Tfx_owned_static Tfx_zero_shadow tfx_segment_000 tfx_segment_001 tfx_segment_002 tfx_segment_003 TfxSyms D_m8 D_8 D_m9 D_10 D_18 D_20 D_30 D_m3c D_m3e D_m40 D_4e D_50 D_6c D_a0 D_150 D_200 D_218 D_21c D_21e D_220 D_270 D_274 D_280 D_2b4 D_2c4 D_2cc D_m3ac D_430 D_440 D_a2c D_1000 D_104c D_10c0 D_10e0 D_10e8 D_10ec D_10f0 D_1100 D_54c0 D_5680 D_m27b919177701d40 D_m10c55b69b38ab717 D_m261b33dfb1afee1d D_332fe4d8b3da5a5b D_558ab28b2f16c771 D_m5c6cf5c3c23d561f D_ma7775317fd2cb971 D_mcf6373b41df84414] in *; img_dfacts.
Ltac img_gen_type_ty_k imgk T :=
let F := eval pattern YB0z.traguard_count, YB0z.traguard_start, YB0z.tramusl_tbl, YB0z.tramusl_text_count, YB0z.tramusl_text_start, YB0z.trasegs, YB0u.tratbl_rtA, YB0u.tratbl_rtA_build, YB0u.tratbl_rtB, YB0u.tratbl_rtB_build, YB0u.tratbl_rtC, YB0u.tratbl_rtC_build, YB0u.tratbl_rtD, YB0u.tratbl_rtD_build, YB0x.tratbl_rtF, YB0x.tratbl_rtF_build, YB0x.tratbl_rtG, YB0x.tratbl_rtG_build, YB0x.tratbl_rtK, YB0x.tratbl_rtK_build, YB0x.tratbl_rtM, YB0x.tratbl_rtM_build, YB10.tra_A_musl_memchr, YB10.tra_A_musl_memcmp, YB10.tra_A_musl_memcpy, YB10.tra_A_musl_memset, YB10.tra_A_musl_strnlen, YF8z.Tra_code, YF90.DRV_TRACES, YF90.TRA_DEPOT, YF90.TRA_ERRNO, YF90.TRA_GP, YF90.TRA_HASH, YF90.TRA_IAL_FLAG, YF90.TRA_IAL_HI, YF90.TRA_IAL_LO, YF90.TRA_IAL_W, YF90.TRA_INST, YF90.TRA_MAIN, YF90.TRA_MAIN_RA, YF90.TRA_OOM, YF90.TRA_STORE, YF90.TRA_TP, YF90.TRA_TR0, YF90.TRA_TSD, YF90.Tra_const, YF90.Tra_const_abs, YF90.Tra_const_shadow, YF90.Tra_const_sym, YF90.Tra_owned_static, YF90.Tra_zero_shadow, Asan.Asan_segment_000, Asan.Asan_segment_001, Asan.Asan_segment_002, Asan.Asan_segment_003, YF90.TraSyms, Asan.M.loaded_segments in T in
lazymatch F with
| ?f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta in (f (@tfxguard_count imgk) (@tfxguard_start imgk) (@tfxmusl_tbl imgk) (@tfxmusl_text_count imgk) (@tfxmusl_text_start imgk) (@tfxsegs imgk) (@tfxtbl_rtA imgk) (@tfxtbl_rtA_build imgk) (@tfxtbl_rtB imgk) (@tfxtbl_rtB_build imgk) (@tfxtbl_rtC imgk) (@tfxtbl_rtC_build imgk) (@tfxtbl_rtD imgk) (@tfxtbl_rtD_build imgk) (@tfxtbl_rtF imgk) (@tfxtbl_rtF_build imgk) (@tfxtbl_rtG imgk) (@tfxtbl_rtG_build imgk) (@tfxtbl_rtK imgk) (@tfxtbl_rtK_build imgk) (@tfxtbl_rtM imgk) (@tfxtbl_rtM_build imgk) (@tfx_A_musl_memchr imgk) (@tfx_A_musl_memcmp imgk) (@tfx_A_musl_memcpy imgk) (@tfx_A_musl_memset imgk) (@tfx_A_musl_strnlen imgk) (@Tfx_code imgk) (@DRV_TRACES imgk) (@TFX_DEPOT imgk) (@TFX_ERRNO imgk) TFX_GP (@TFX_HASH imgk) (@TFX_IAL_FLAG imgk) (@TFX_IAL_HI imgk) (@TFX_IAL_LO imgk) (@TFX_IAL_W imgk) (@TFX_INST imgk) (@TFX_MAIN imgk) (@TFX_MAIN_RA imgk) (@TFX_OOM imgk) (@TFX_STORE imgk) (@TFX_TP imgk) (@TFX_TR0 imgk) (@TFX_TSD imgk) (@Tfx_const imgk) (@Tfx_const_abs imgk) (@Tfx_const_shadow imgk) (@Tfx_const_sym imgk) (@Tfx_owned_static imgk) (@Tfx_zero_shadow imgk) (@tfx_segment_000 imgk) (@tfx_segment_001 imgk) (@tfx_segment_002 imgk) (@tfx_segment_003 imgk) (@TfxSyms imgk) (@tfxsegs imgk))
end.
Ltac img_gen_type_k imgk c := let T := type of c in let T' := img_gen_type_ty_k imgk T in exact T'.
Ltac img_gen_type c := lazymatch goal with imgk : img |- _ => img_gen_type_k imgk c end.
Section j. Context {fx : YK11.FPState} {rc : YN05.RunCeil} {imgk : img}.

Lemma tfxmusl_tbl_ok : ltac:(img_gen_type YB0z.tramusl_tbl_ok).
Proof. destruct imgk; [(exact YB0z.tramusl_tbl_ok) | (exact YB1u.trbmusl_tbl_ok)]. Qed.

Lemma tfxtbl_rtA_ok : ltac:(img_gen_type YB0u.tratbl_rtA_ok).
Proof. destruct imgk; [(exact YB0u.tratbl_rtA_ok) | (exact YB1p.trbtbl_rtA_ok)]. Qed.

Lemma tfxtbl_rtB_ok : ltac:(img_gen_type YB0u.tratbl_rtB_ok).
Proof. destruct imgk; [(exact YB0u.tratbl_rtB_ok) | (exact YB1p.trbtbl_rtB_ok)]. Qed.

Lemma tfxtbl_rtC_ok : ltac:(img_gen_type YB0u.tratbl_rtC_ok).
Proof. destruct imgk; [(exact YB0u.tratbl_rtC_ok) | (exact YB1p.trbtbl_rtC_ok)]. Qed.
Lemma tfxtbl_rtD_eq : ltac:(img_gen_type YB0u.tratbl_rtD_eq).
Proof. destruct imgk; [(exact YB0u.tratbl_rtD_eq) | (exact YB1p.trbtbl_rtD_eq)]. Qed.
Lemma tfxtbl_rtD_ok : ltac:(img_gen_type YB0u.tratbl_rtD_ok).
Proof. destruct imgk; [(exact YB0u.tratbl_rtD_ok) | (exact YB1p.trbtbl_rtD_ok)]. Qed.

Lemma tfxtbl_rtF_ok : ltac:(img_gen_type YB0x.tratbl_rtF_ok).
Proof. destruct imgk; [(exact YB0x.tratbl_rtF_ok) | (exact YB1s.trbtbl_rtF_ok)]. Qed.

Lemma tfxtbl_rtG_ok : ltac:(img_gen_type YB0x.tratbl_rtG_ok).
Proof. destruct imgk; [(exact YB0x.tratbl_rtG_ok) | (exact YB1s.trbtbl_rtG_ok)]. Qed.

Lemma tfxtbl_rtK_ok : ltac:(img_gen_type YB0x.tratbl_rtK_ok).
Proof. destruct imgk; [(exact YB0x.tratbl_rtK_ok) | (exact YB1s.trbtbl_rtK_ok)]. Qed.

Lemma tfxtbl_rtM_ok : ltac:(img_gen_type YB0x.tratbl_rtM_ok).
Proof. destruct imgk; [(exact YB0x.tratbl_rtM_ok) | (exact YB1s.trbtbl_rtM_ok)]. Qed.
Lemma ts_inst (B : asyms) (TS_ : TfxSyms B) : as_inst B = TFX_INST.
Proof. destruct imgk; [exact (YF90.ts_inst B TS_) | exact (YF9j.ts_inst B TS_)]. Qed.
Lemma ts_tp (B : asyms) (TS_ : TfxSyms B) : as_tp B = TFX_TP.
Proof. destruct imgk; [exact (YF90.ts_tp B TS_) | exact (YF9j.ts_tp B TS_)]. Qed.
Lemma ts_tsd (B : asyms) (TS_ : TfxSyms B) : as_tsd B = TFX_TSD.
Proof. destruct imgk; [exact (YF90.ts_tsd B TS_) | exact (YF9j.ts_tsd B TS_)]. Qed.
Lemma ts_gp (B : asyms) (TS_ : TfxSyms B) : as_gp B = TFX_GP.
Proof. destruct imgk; [exact (YF90.ts_gp B TS_) | exact (YF9j.ts_gp B TS_)]. Qed.
Lemma ts_code (B : asyms) (TS_ : TfxSyms B) : as_code B = Tfx_code.
Proof. destruct imgk; [exact (YF90.ts_code B TS_) | exact (YF9j.ts_code B TS_)]. Qed.
Lemma ts_errno (B : asyms) (TS_ : TfxSyms B) : as_errno B = TFX_ERRNO.
Proof. destruct imgk; [exact (YF90.ts_errno B TS_) | exact (YF9j.ts_errno B TS_)]. Qed.
Lemma ts_depot (B : asyms) (TS_ : TfxSyms B) : as_depot B = TFX_DEPOT.
Proof. destruct imgk; [exact (YF90.ts_depot B TS_) | exact (YF9j.ts_depot B TS_)]. Qed.
Lemma ts_store (B : asyms) (TS_ : TfxSyms B) : as_store B = TFX_STORE.
Proof. destruct imgk; [exact (YF90.ts_store B TS_) | exact (YF9j.ts_store B TS_)]. Qed.
Lemma ts_ial_lo (B : asyms) (TS_ : TfxSyms B) : as_ialloc_lo B = TFX_IAL_LO.
Proof. destruct imgk; [exact (YF90.ts_ial_lo B TS_) | exact (YF9j.ts_ial_lo B TS_)]. Qed.
Lemma ts_ial_hi (B : asyms) (TS_ : TfxSyms B) : as_ialloc_hi B = TFX_IAL_HI.
Proof. destruct imgk; [exact (YF90.ts_ial_hi B TS_) | exact (YF9j.ts_ial_hi B TS_)]. Qed.
Lemma ts_ial_w (B : asyms) (TS_ : TfxSyms B) : as_ialloc_w B = TFX_IAL_W.
Proof. destruct imgk; [exact (YF90.ts_ial_w B TS_) | exact (YF9j.ts_ial_w B TS_)]. Qed.
Lemma ts_ial_flag (B : asyms) (TS_ : TfxSyms B) : as_ialloc_flag B = TFX_IAL_FLAG.
Proof. destruct imgk; [exact (YF90.ts_ial_flag B TS_) | exact (YF9j.ts_ial_flag B TS_)]. Qed.
Lemma ts_oom (B : asyms) (TS_ : TfxSyms B) : as_oom_byte B = TFX_OOM.
Proof. destruct imgk; [exact (YF90.ts_oom B TS_) | exact (YF9j.ts_oom B TS_)]. Qed.
Lemma ts_ok (B : asyms) (TS_ : TfxSyms B) : asyms_ok B.
Proof. destruct imgk; [exact (YF90.ts_ok B TS_) | exact (YF9j.ts_ok B TS_)]. Qed.
Lemma ts_owned (B : asyms) (TS_ : TfxSyms B) : as_owned_static B = Tfx_owned_static.
Proof. destruct imgk; [exact (YF90.ts_owned B TS_) | exact (YF9j.ts_owned B TS_)]. Qed.
Lemma ts_const (B : asyms) (TS_ : TfxSyms B) : forall ly, as_const B ly = Tfx_const ly.
Proof. destruct imgk; [exact (YF90.ts_const B TS_) | exact (YF9j.ts_const B TS_)]. Qed.
Lemma ts_junk (B : asyms) (TS_ : TfxSyms B) : forall ly r, In r (as_junk B ly) -> exists z, fst r = ANum z /\ (0xa1000 + D_1000) <= z /\ z + snd r <= (0x5ff000 + D_1000).
Proof. destruct imgk; [exact (YF90.ts_junk B TS_) | exact (YF9j.ts_junk B TS_)]. Qed.
Lemma ts_junk_comb (B : asyms) (TS_ : TfxSyms B) : forall ly, In (ANum (TFX_INST + o_comb_stats), 40) (as_junk B ly).
Proof. destruct imgk; [exact (YF90.ts_junk_comb B TS_) | exact (YF9j.ts_junk_comb B TS_)]. Qed.
Lemma ts_junk_ly (B : asyms) (TS_ : TfxSyms B) : forall ly ly', as_junk B ly' = as_junk B ly.
Proof. destruct imgk; [exact (YF90.ts_junk_ly B TS_) | exact (YF9j.ts_junk_ly B TS_)]. Qed.
Lemma ts_zsh (B : asyms) (TS_ : TfxSyms B) : as_zero_shadow B = Tfx_zero_shadow.
Proof. destruct imgk; [exact (YF90.ts_zsh B TS_) | exact (YF9j.ts_zsh B TS_)]. Qed.
Lemma ts_universe (B : asyms) (TS_ : TfxSyms B) : universe_ok (as_universe B).
Proof. destruct imgk; [exact (YF90.ts_universe B TS_) | exact (YF9j.ts_universe B TS_)]. Qed.
Lemma ts_universe_drv (B : asyms) (TS_ : TfxSyms B) : forall t, In t DRV_TRACES -> In t (as_universe B).
Proof. destruct imgk; [exact (YF90.ts_universe_drv B TS_) | exact (YF9j.ts_universe_drv B TS_)]. Qed.
Lemma ts_hash (B : asyms) (TS_ : TfxSyms B) : forall h, (h < 2)%nat -> (as_dhash B (TFX_TR0 h)) mod 2 ^ 64 = TFX_HASH h.
Proof. destruct imgk; [exact (YF90.ts_hash B TS_) | exact (YF9j.ts_hash B TS_)]. Qed.
End j.
