(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjz.v (a working branch 86aa4177b94, file sha256 c6599b9f620c) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 18 image addresses moved by code-verified function pairs (22 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the second 0xa5ad0 of the owned static range, which the relocation tool left at its cgif value, is 0xa7790 as in fs's AFjz.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AB1q AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm AFia AFib AGid AGie AGif AGig.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGjv AGjw AGjx AGjh AGjn AGjo AGjk AGjl AGjp AGjq AGjs AGju AGjt AGjy.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; zlia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := eval vm_compute in (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
eq_refl eq_refl ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS
end.
Section f.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let INSTv : Z := bv_unsigned (getr regs0 11).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@AGjm.R8v n).
Local Abbreviation N8D := (@AGjm.N8D n).
Local Abbreviation NDv := (@AGjm.NDv n).
Local Abbreviation MSv := (@AGjm.MSv n).
Local Abbreviation QSv := (@AGjm.QSv ly idx).
Local Abbreviation Kv := (@AGjm.Kv mb).
Local Abbreviation Uv := (@AGjm.Uv mb).
Local Abbreviation SMv := (@AGjm.SMv mb).
Local Abbreviation PBv := (@AGjm.PBv n mb).
Local Abbreviation BSLv := (@AGjm.BSLv regs0 n).
Local Abbreviation E0 := (@AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@AGjm.E1 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@AGjm.E2 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@AGjm.E10 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E11 := (@AGjm.E11 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@AGjm.EaT ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@AGjm.EaC ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@AGjm.EaSB ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@AGjm.EaTOP ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQ := (@AGjm.EaQ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRES := (@AGjm.EaRES ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaNCH := (@AGjm.EaNCH ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@AGjm.EaMS ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@AGjm.EaMAP ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaEND := (@AGjm.EaEND ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSHB := (@AGjm.EaSHB ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTL := (@AGjm.EaTL ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQS := (@AGjm.EaQS ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaBSL := (@AGjm.EaBSL ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSM := (@AGjm.EaSM ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaUE := (@AGjm.EaUE ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaND := (@AGjm.EaND ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRL := (@AGjm.EaRL ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaN8D := (@AGjm.EaN8D ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaPB := (@AGjm.EaPB ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + AFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis Hso : sp0 <= SOv /\ SOv + 16 <= ly_stk_hi ly /\ SOv mod 8 = 0.
Hypothesis Hbp : sp0 <= BPv /\ BPv + 8 * 30 <= ly_stk_hi ly /\ BPv mod 8 = 0.
Hypothesis Hinst : 0x9f000 <= INSTv /\ INSTv + 0xe60 <= 0x12a1a0 /\ INSTv mod 8 = 0.
Hypothesis Nrange : 64513 <= n < SEC_NMAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation size_facts := (@AGjm.size_facts n Nrange).
Local Abbreviation high_facts := (@AGjm.high_facts _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@AGjm.map_facts _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation map_zoneN := (@AGjm.map_zoneN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation map_off_img := (@AGjm.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@AGjm.WINT ly).
Local Abbreviation WINI := (@AGjm.WINI regs0 n).
Local Abbreviation BSLv_range := (@AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx).
Variables (mat0 : list word).
Let H0 := w_H W.
(* The registers at Allocate's entry, over the virtual regs0 of E0 (AGhy.REGS_G). *)
Variable regsU : bvmap 5 word.
Let cfg0 : config := mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Local Abbreviation off_T := (@AGjm.off_T _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Local Abbreviation off_C := (@AGjm.off_C _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Local Abbreviation off_Q := (@AGjm.off_Q _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Local Abbreviation off_NB := (@AGjm.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGjm.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@AGjm.off_shadow ly regs0 tr idx res mb Htrlen Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation DZONE := (@AGjm.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@AGjm.at_S _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_runP := (@AGjm.at_S_runP _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@AGjm.at_S_runM _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@AGjm.at_S_run_ecallP _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@AGjm.at_S_run_ecallM _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@AGjm.at_S_pin _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@AGjm.at_S_arm _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@AGjm.at_S_forget _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@AGjm.at_S_noconds _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@AGjm.at_S_eq _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation sv_denot_SOff0 := (@AGjm.sv_denot_SOff0).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
(* The walk's instance (register 11 at Allocate's entry) is the model's allocator instance. *)
Hypothesis Hinst_eq : as_inst B = INSTv.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4.
Hypothesis Hj5 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5.
Hypothesis Hj9 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9.
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) (INSTv + o_comb_stats + 16) 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) (INSTv + o_comb_stats + 24) 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (INSTv + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (INSTv + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (INSTv + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Lemma INSTv_TFIB : INSTv = TFIB_INST.
Proof. rewrite <- Hinst_eq. exact (ts_inst B TS). Qed.
Local Abbreviation RES2T_ne := (@AGjl.RES2T_ne ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@AGjl.RES2T_eq ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation lyF := (@AGjy.lyF ly mb S).
Local Abbreviation SFS := (@AGjy.SFS n tr S).
Local Abbreviation KSc := (@AGjy.KSc n S).
Local Abbreviation lyF_le := (@AGjy.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@AGjy.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@AGjy.lyF_eqs ly mb S).
Local Abbreviation sizes_model := (@AGjy.sizes_model ly regs0 n tr res Htrlen Hinst Nrange S).
Local Abbreviation SF_parts := (@AGjy.SF_parts n tr res S Hres_def).
Local Abbreviation SEF := (@AGjy.SEF _ W ly regs0 mem0 n tr res mb Htrlen Hinst Nrange B S HARm Hres_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?EaQS, ?EaBSL, ?EaSM, ?EaPB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, UNW_STK, BST_SIZE, AFSTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?EaQ, ?EaMAP, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Ltac s_station HR ss' :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_eq Wx md X P ss ss' W' c' HR ltac:(vm_compute; reflexivity)) as H2; clear HR; rename H2 into HR end.
Local Ltac s_runP HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runP Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_runM HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runM Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_ecallP HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallP Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac s_ecallM HR tbl tblok ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
eapply (at_S_run_ecallM Wx tbl tblok 0x7ffffff0 md X P ss ss' W' c' HR);
[ vm_compute; reflexivity | reflexivity | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ] end.
Local Ltac unfold_atoms := unfold aT, aC, aSB, aTOP, aLEN, aJ0, aR8, aQ, aRES, aNCH, aMS, aMAP, aEND, aSHB, aTL, aQS, aBSL, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aSM, aUE, aND, aRL, aN8DS, aPBS.
Local Ltac pin_zevS := apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_pin HR r e :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let t := eval vm_compute in (sr_get (ss_regs ss) r) in
let HU := fresh "HU" in
assert (HU : U E0 e = U E0 t);
[ | let H2 := fresh "HR" in
pose proof (at_S_pin Wx md X P ss W' c' r e HR ltac:(intros XX; discriminate XX) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HU) as H2;
clear HU HR; rename H2 into HR ] end.
Local Ltac s_arm HR cnd tk a b :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HB := fresh "HB" in
assert (HB : branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk);
[ | let H2 := fresh "HR" in
pose proof (at_S_arm Wx md X P ss W' c' cnd tk a b HR ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HB) as H2;
clear HB HR; rename H2 into HR ] end.
Local Ltac s_forget HR k clob :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_forget Wx md X P ss W' c' k clob HR ltac:(unfold sHAV; cbv; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HR; rename H2 into HR end.
Local Ltac s_noconds HR :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_S_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Local Ltac arm_zevS := rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_eq_U, ?branch_ne_U;
rewrite !U_zev by (vm_compute; reflexivity); cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac U_zevS := rewrite U_zev by reflexivity; cbn [zev zalu_raw zmd_raw]; unfold rho_of; try unfold_atoms.
Local Ltac s_armR HR cnd tk r1 r2 :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let a := eval vm_compute in (sr_get (ss_regs ss) r1) in
let b := eval vm_compute in (sr_get (ss_regs ss) r2) in
s_arm HR cnd tk a b end.
Local Ltac ladder_arith Z :=
let MF := fresh "MF" in let SF := fresh "SF" in let NRx := fresh "NRx" in
pose proof map_facts as MF; pose proof size_facts as SF; pose proof Nrange as NRx;
arm_zevS; rewrite ?EaSHB, ?EaMAP, ?EaEND, ?EaTL, ?EaUE, ?EaRL, ?EaN8D, ?EaND, ?EaMS; unfold w64;
clear - Z MF SF NRx;
destruct MF as (M1x & M2x & M3x & K4x & U5x & E6x & UE7x & E8x & UE9x & MTx & MUx & SM1x & SM2x & SM3x & PBx & SMAx);
destruct SF as (Z1x & Z2x & Z3x & Z4x & Z5x & Z6x & Z7x & Z8x & Z9x & Z10x & Z11x & Z12x & Z13x & Z14x);
unfold AGjm.SHBv, AGjm.Kv, AGjm.Uv, AGjm.SMv, AGjm.PBv, SEC_NMAX,
kLowShadowBeg, kHighShadowEnd, TFIB_IMG_END in *;
rewrite !unsigned_lit_small by zlia; zcanon_simp;
first [ rewrite (proj2 (Z.ltb_ge _ _)) by zlia | rewrite (proj2 (Z.ltb_lt _ _)) by zlia ]; reflexivity.
Local Ltac s_join HR k clob SJ := s_forget HR k clob; s_noconds HR; s_station HR SJ; apply SRr_ret; exact HR.
Local Ltac s_ladder RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok 0x5449c Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x542f4 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5449c Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x544dc Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderW RUN HR tbl tblok STOP Sl Slo Sh Sh2 Sh3a Sh3 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok 0x5449c Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x542f4 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5449c Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x544d8 Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x544dc Sh3 HX HP;
s_armR HR BC_GEU false (5%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Local Ltac s_ladderM RUN HR tbl tblok STOP Slo Sh Sh2 Shi SJ k clob HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let HQ := fresh "HQ" in
assert (HQ : SRr tfibsegs W' c' (at_S Wx md X P SJ));
[ let MZ := fresh "MZ" in pose proof map_zoneN as MZ; destruct MZ as [ZLO|ZHI];
[ s_armR HR BC_GEU true (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (12%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x32414 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x32418 Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition FQ (Wz : world tfibsegs) (grow : bool) (m : word -> option byte) : Prop :=
let mr := mrestrict (w_H Wz) m in
val_mem tfibsegs mr QSv 8 mb /\ val_mem tfibsegs mr mb 8 mb /\ val_mem tfibsegs mr (mb + 8) 8 MSv /\ val_mem tfibsegs mr (mb + 16) 8 NDv /\ val_mem tfibsegs mr (mb + 24) 8 idx /\
val_mem tfibsegs mr Kv 8 0xCC6E96B9CC6E96B9 /\ val_mem tfibsegs mr (Kv + 8) 8 (Uv - 16) /\ val_mem tfibsegs mr (Uv - 16) 1 2 /\ val_mem tfibsegs mr (Uv - 15) 1 17 /\
val_mem tfibsegs mr (Uv - 14) 2 0 /\ val_mem tfibsegs mr (Uv - 12) 4 n /\ val_mem tfibsegs mr (T + t_unwinding) 1 0 /\
val_mem tfibsegs mr (INSTv + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res) /\ val_mem tfibsegs mr (INSTv + o_sec_n) 8 (idx + 1) /\
val_mem tfibsegs mr (INSTv + o_sec_mutex) 1 0 /\ val_mem tfibsegs mr (INSTv + o_sec_mutex + 1) 1 0 /\ val_mem tfibsegs mr (INSTv + o_sec_mutex + 2) 2 0 /\
(forall a, WINT a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144) -> apresent (w_H Wz) m a) /\
(forall a, WINI a -> aview tfibsegs (w_H Wz) m a <> None).
Section g.
Variables (Wz : world tfibsegs) (grow : bool).
Hypothesis Hgrow : grow = true <-> idx = res.
Lemma srl32_n : Z.shiftr n 32 = 0.
Proof. clearP. pose proof Nrange as NR. unfold SEC_NMAX in NR. rewrite Z.shiftr_div_pow2 by zlia. apply Z.div_small. zlia. Qed.
(* FQ from any state whose memory is Ue_RET's (Ue_RET0, the can_fill = 0 end, has the same memory). *)
Lemma FQ_mem_e : forall ss (E' : env) ms, ss_mem ss = ss_mem Ue_RET -> env_agree sHAV E0 E' -> st_ok tfibsegs E' ss (restrict (w_H Wz) ms) -> FQ Wz grow (ms_mem ms).
Proof.
intros [pc rg fr mm rv fc] E' ms Hm HE HS. cbn [ss_mem] in Hm. subst mm. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, SEC_NMAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; apply unsigned_lit_small; zlia).
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; try unfold T; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; zlia).
assert (UI : bv_unsigned (ew E' 11) = INSTv) by (rewrite (HEn 11%nat ltac:(unfold sHAV; zlia)), E11; reflexivity).
unfold FQ. cbv zeta.
split. { memv HS 1%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UQS; zlia | rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; reflexivity | zlia]. }
split. { memv HS 2%nat 10%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; reflexivity | zlia]. }
split. { memv HS 2%nat 9%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 42%nat ltac:(unfold sHAV; zlia)), EaMS; reflexivity | zlia]. }
split. { memv HS 2%nat 8%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 63%nat ltac:(unfold sHAV; zlia)), EaND; reflexivity | unfold NDv, R8v in *; zlia]. }
split. { memv HS 2%nat 7%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; reflexivity | zlia]. }
split. { memv HS 2%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Kv; zlia | reflexivity | zlia]. }
split. { memv HS 2%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Kv; zlia | | unfold Uv; zlia].
cbn [sv_denot]. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned. f_equal. zlia. }
split. { memv HS 2%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | reflexivity | zlia]. }
split. { memv HS 2%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | reflexivity | zlia]. }
split. { memv HS 2%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. change (Z.land (zcanon 32) 63) with 32. rewrite srl32_n. reflexivity. }
split. { memv HS 2%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | cbn [sv_denot]; rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 44%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UT; unfold t_unwinding; zlia | reflexivity | zlia]. }
split. { memv HS 52%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | | destruct grow; unfold kPtrArrayEntriesPerCommit; zlia].
change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(vm_compute; reflexivity)).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_small. zlia. }
split. { memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 56%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | reflexivity | zlia]. }
split. { memv HS 56%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite UI; unfold o_sec_mutex; lia | reflexivity | zlia]. }
split. { memv HS 56%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite UI; unfold o_sec_mutex; lia | reflexivity | zlia]. }
split.
{ intros a Ha. destruct Ha as [Hw|[Hq|Hm]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 46%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 47%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; unfold t_unwinding in *; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, t_unwinding in *; try unfold T in *; zlia) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 1%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UQS; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; unfold QSv in *; try unfold Qb in *; zlia) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 2%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UMAP; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) ]. }
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB Hinst MZ; unfold WINI, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *; zlia).
apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (INSTv + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (INSTv + 128)) as [A2|A2]].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 52%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_reserved in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_sorted in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_stats in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 62%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_mutex in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_comb_stats in *; zlia]. }
Qed.
Lemma FQ_mem_o : n mod 8 <> 0 -> forall ss (E' : env) ms, ss_mem ss = ss_mem Uo_RET -> env_agree sHAV E0 E' -> st_ok tfibsegs E' ss (restrict (w_H Wz) ms) ->
FQ Wz grow (ms_mem ms) /\ val_mem tfibsegs (mrestrict (w_H Wz) (ms_mem ms)) PBv 1 (n mod 8) /\ apresent (w_H Wz) (ms_mem ms) PBv.
Proof.
intros H8 [pc rg fr mm rv fc] E' ms Hm HE HS. cbn [ss_mem] in Hm. subst mm. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, SEC_NMAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; apply unsigned_lit_small; zlia).
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; try unfold T; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; zlia).
assert (UI : bv_unsigned (ew E' 11) = INSTv) by (rewrite (HEn 11%nat ltac:(unfold sHAV; zlia)), E11; reflexivity).
assert (UPB : bv_unsigned (ew E' 66) = PBv).
{ rewrite (HEn 66%nat ltac:(unfold sHAV; zlia)), EaPB. unfold w64. apply unsigned_lit_small. pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _).
pose proof (Z.div_mod N8D 8 ltac:(zlia)) as DM8. pose proof (Z.mod_pos_bound N8D 8 ltac:(zlia)) as MB8. pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8'. pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)) as MB8'. clear - PB SM1 SM2 Z4 Z8 DM8 MB8 DM8' MB8' NR MZ. zlia. }
split; [| split].
2:{ memv HS 0%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UPB; zlia | | pose proof (Z.mod_pos_bound n 8 ltac:(zlia)); zlia].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. change (zcanon 7) with (Z.ones 3). rewrite Z.land_ones by zlia. change (2 ^ 3) with 8.
apply zcanon_small. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)). zlia. }
2:{ pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _).
pose proof (Z.div_mod N8D 8 ltac:(zlia)) as DM8. pose proof (Z.mod_pos_bound N8D 8 ltac:(zlia)) as MB8. pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8'. pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)) as MB8'.
eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 0%nat _ PBv HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UPB; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - PB SM1 SM2 Z4 Z8 DM8 MB8 DM8' MB8' NR MZ; zlia) ]. }
unfold FQ. cbv zeta.
split. { memv HS 2%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UQS; zlia | rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; reflexivity | zlia]. }
split. { memv HS 3%nat 10%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; reflexivity | zlia]. }
split. { memv HS 3%nat 9%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 42%nat ltac:(unfold sHAV; zlia)), EaMS; reflexivity | zlia]. }
split. { memv HS 3%nat 8%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 63%nat ltac:(unfold sHAV; zlia)), EaND; reflexivity | unfold NDv, R8v in *; zlia]. }
split. { memv HS 3%nat 7%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; zlia | rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; reflexivity | zlia]. }
split. { memv HS 3%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Kv; zlia | reflexivity | zlia]. }
split. { memv HS 3%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Kv; zlia | | unfold Uv; zlia].
cbn [sv_denot]. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned. f_equal. zlia. }
split. { memv HS 3%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | reflexivity | zlia]. }
split. { memv HS 3%nat 3%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | reflexivity | zlia]. }
split. { memv HS 3%nat 6%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | | zlia].
lazymatch goal with |- sv_denot ?E ?t = _ => rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E t)); f_equal; change (bv_unsigned (sv_denot E t)) with (U E t); rewrite (U_zev E t eq_refl) end.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite Z.add_0_r, (zcanon_small n) by zlia. change (Z.land (zcanon 32) 63) with 32. rewrite srl32_n. reflexivity. }
split. { memv HS 3%nat 5%nat; [cbn [base_val YP09.r_base]; rewrite UMAP; unfold Uv; zlia | cbn [sv_denot]; rewrite (HEn 10%nat ltac:(unfold sHAV; zlia)), E10, Hn; unfold w64; rewrite ?Zbv_add_unsigned, ?Z.add_0_r; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 45%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UT; unfold t_unwinding; zlia | reflexivity | zlia]. }
split. { memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | | destruct grow; unfold kPtrArrayEntriesPerCommit; zlia].
change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(vm_compute; reflexivity)).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_small. zlia. }
split. { memv HS 54%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 57%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UI; reflexivity | reflexivity | zlia]. }
split. { memv HS 57%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite UI; unfold o_sec_mutex; lia | reflexivity | zlia]. }
split. { memv HS 57%nat 2%nat; [cbn [base_val YP09.r_base]; rewrite UI; unfold o_sec_mutex; lia | reflexivity | zlia]. }
split.
{ intros a Ha. destruct Ha as [Hw|[Hq|Hm]].
- unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
* eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 46%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 47%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 48%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 45%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; unfold t_unwinding in *; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, t_unwinding in *; try unfold T in *; zlia) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 2%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UQS; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; unfold QSv in *; try unfold Qb in *; zlia) ].
- eapply (st_ok_window_apresent_off (w_H Wz) E' _ _ 3%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UMAP; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) ]. }
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB Hinst MZ; unfold WINI, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *; zlia).
apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (INSTv + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (INSTv + 128)) as [A2|A2]].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_reserved in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_sorted in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_stats in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 63%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_sec_mutex in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 58%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UI; unfold o_comb_stats in *; zlia]. }
Qed.
Lemma FQ_e : forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Ue_RET (restrict (w_H Wz) ms) -> FQ Wz grow (ms_mem ms).
Proof. intros E' ms HE HS. exact (FQ_mem_e Ue_RET E' ms eq_refl HE HS). Qed.
Lemma FQ_o : n mod 8 <> 0 -> forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Uo_RET (restrict (w_H Wz) ms) ->
FQ Wz grow (ms_mem ms) /\ val_mem tfibsegs (mrestrict (w_H Wz) (ms_mem ms)) PBv 1 (n mod 8) /\ apresent (w_H Wz) (ms_mem ms) PBv.
Proof. intros H8 E' ms HE HS. exact (FQ_mem_o H8 Uo_RET E' ms eq_refl HE HS). Qed.
Lemma FQ_e0 : forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Ue_RET0 (restrict (w_H Wz) ms) -> FQ Wz grow (ms_mem ms).
Proof. intros E' ms HE HS. exact (FQ_mem_e Ue_RET0 E' ms ltac:(vm_compute; reflexivity) HE HS). Qed.
Lemma FQ_o0 : n mod 8 <> 0 -> forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Uo_RET0 (restrict (w_H Wz) ms) ->
FQ Wz grow (ms_mem ms) /\ val_mem tfibsegs (mrestrict (w_H Wz) (ms_mem ms)) PBv 1 (n mod 8) /\ apresent (w_H Wz) (ms_mem ms) PBv.
Proof. intros H8 E' ms HE HS. exact (FQ_mem_o H8 Uo_RET0 E' ms ltac:(vm_compute; reflexivity) HE HS). Qed.
End g.
Lemma OWN_T : forall a, WINT a -> aowned B ly S a.
Proof.
clearP. intros a Hw. apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto|].
cbn [fst snd]. unfold WINT, t_unwinding, kThreadObjSize in *. unfold T in Hw. clear - Hw. zlia.
Qed.
Lemma OWN_I : forall a, WINI a -> aowned B ly S a.
Proof.
clearP. intros a Hw. pose proof BSLv_range as HB. pose proof INSTv_TFIB as EIn. apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa48d8, 0xa7788 - 0xa48d8). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd].
unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. clear - Hw HB EIn. zlia.
Qed.
Lemma OWN_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> aowned B ly S a.
Proof. clearP. intros a Ha. apply (own_core B ly S rd0 (ly_Q ly, kPtrArrayResv) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]; unfold Qb in Ha; exact Ha]. Qed.
Lemma OWN_D : forall a, DZONE a -> aowned B ly S a.
Proof.
clearP. intros a Hd. unfold DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa7790, 0x5ca590 - 0xa7790). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd]. clear - Hd. zlia.
- apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Hd].
- apply (own_core B ly S rd0 (ly_SB ly, kStoreBlockSize) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Hd].
Qed.
Lemma band_core : forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
clearP. intros a Ha. apply Exists_exists. pose proof hm_zone_shadow as [E1 E2].
destruct Ha as [LO|HI].
- exists lm_zone. split; [repeat (apply in_app_iff; right); right; left; reflexivity|].
unfold in_zr, lm_zone, shadow_addr, SHADOW_OFF. cbn [fst snd]. clear - LO. unfold kLowMemEnd, kLowShadowBeg, kLowShadowEnd in *.
repeat match goal with |- context[(?x + 7) / 8] => let v := eval vm_compute in ((x + 7) / 8) in change ((x + 7) / 8) with v end. change (0 / 8) with 0. zlia.
- exists hm_zone. split; [repeat (apply in_app_iff; right); left; reflexivity|].
unfold in_zr. cbn [fst snd] in *. rewrite E1. rewrite E1 in E2. clear - HI E2. zlia.
Qed.
Lemma OWN_SH : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
forall a, SMv <= a < SMv + MSv / 8 -> aowned B ly S a.
Proof.
intros GAP a Ha. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
split; [do 4 right; apply band_core; clear - Ha MZ; unfold kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; zlia|].
pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. assert (M8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
eapply (nc_shadow B ly S rd0 a mb MSv HARm).
- apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp. replace (p * 4096) with ((p * 512) * 8) by zlia. apply Z.mod_mul. zlia.
- clear - M1 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. zlia.
- clear - M2 MZ. ceil; unfold ASAN_CEIL, kHighMemEnd in *. zlia.
- apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto.
- rewrite <- SMA. replace ((MSv + 7) / 8) with (MSv / 8); [clear - Ha MZ; zlia|].
clear - M8 Z8 MZ. apply Z.mod_divide in M8 as [u Hu]; [|zlia]. rewrite Hu. rewrite Z.div_mul by zlia. rewrite Z.div_add_l by zlia. change (7 / 8) with 0. zlia.
Qed.
Lemma OWN_BANDhid : AR tfibsegs B ly S W mem0 md0 -> forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) -> w_H W (Z_to_bv 64 a) = true -> aowned B ly S a.
Proof.
intros HAR a Ha Hh. split; [do 4 right; apply band_core; exact Ha|].
assert (HB : in_band_rw a) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; zlia).
intros C. apply (client_band_vis B ly S rd0 a HARm HB C). unfold rd0. apply aview_band_hidden; [exact (al_img_env tfibsegs ly S _ LY (proj1 (proj2 HAR))) | exact HB | exact Hh].
Qed.
Lemma NEWOWN : forall (grow : bool) (z : Z),
Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
forall a, mb <= a < mb + MSv -> ~ (Uv <= a < Uv + n) -> aowned B lyF (SFS grow z) a.
Proof.
intros grow z GAP a Ha Hnu. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof (SF_parts grow z) as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). destruct Hmap_apart as (_ & _ & MP3 & _).
split.
- do 3 right. left. rewrite (SEF grow z). apply Exists_exists. exists (mb, MSv). split; [apply in_app_iff; right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- intros [(k & Hk & Hst & Hr)|(cp & Hcp & Hr)].
+ rewrite Rck in Hk. apply in_app_iff in Hk as [Hk|[<-|[]]].
*
unfold ck_user in Hr. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (AFib.padd_lt S _ _ (AFib.chunk_lt S _ _ _ _ WF k Hk))) in Hr.
fold (ck_user k) in Hr. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
destruct (extent_zone B ly S rd0 k HARm Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
-- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - Ha Hr X1 X2 MP3 G8 G5 MZ. zlia.
-- pose proof (proj1 (Forall_forall _ _) GAP (m, len) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - Ha Hr X1 X2 D G8 G5 MZ. unfold kPage in *. zlia.
*
apply Hnu. unfold ck_user in Hr. cbn [YG00.ck_beg KSc AFib.KS padd sptr_addr sptr_exp aeval] in Hr.
change (YG00.ck_rz (AFib.KS S n)) with (ck_rz KSc) in Hr. rewrite KR, KN, lyF_sec in Hr. unfold Uv. unfold kPage in Hr. clear - Hr MZ. zlia.
+
unfold frames in Hcp, Rfr. rewrite Rfr in Hcp. destruct cp as [cid pos]. cbn [fst snd] in Hr.
pose proof (YG0s.frame_facts B ly S rd0 cid pos HARm Hcp) as (C1 & C2 & F1 & F2 & FA & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(zlia) ltac:(zlia)).
pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). unfold frame_addr, in_zr in Hr. rewrite E6 in Hr. cbn [fst snd] in Hr.
pose proof (proj1 (Forall_forall _ _) GAP (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
destruct Hr as [Hr|Hr].
* clear - Ha Hr D P1 P2 C1 H MZ. unfold kFakeFramesOff in *. zlia.
* pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 P1 H MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kFakeFramesOff in *; zlia) ltac:(clear - P4 MZ; zlia) ltac:(clear - F1 P2 MZ; ceil; unfold zone3, TFIB_IMG_LO, in_app, ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg, kFakeStackSize in *; zlia)) as SBel.
pose proof (Z.div_pos (ly_F ly + fs_frame_off cid pos) 8 ltac:(clear - F1 P1 H MZ; unfold in_app, kFakeFramesOff in *; zlia) ltac:(zlia)) as SB0.
clear - Ha Hr SBel SB0 M1 MZ. unfold shadow_addr, SHADOW_OFF, zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. zlia.
Qed.
End f.
End d.
