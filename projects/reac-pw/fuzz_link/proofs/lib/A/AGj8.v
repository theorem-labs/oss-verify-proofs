(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGj8.v (a working branch 95e6f1d72b6, file sha256 ac53a727f00c; written for cgif_file_fuzzer.asan-ubsan 1c29845fe605) onto libreac/fuzz_decode's asan image (pin 5973b76807d8, unstripped twin 4cb0a852e826); module paths changed, names TfibSyms -> GrantSyms; its 6 image addresses moved by code-verified function pairs (6 port_addr_check 0767e70e074a MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1w AE3d AFhy AGhy AFi1 AGj6 AGhz AGi2 AGi4.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
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
Section e.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (tr : list Z).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let SOv : Z := bv_unsigned (getr regs0 13).
Let BPv : Z := bv_unsigned (getr regs0 12).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation RZ := (@AGj6.RZ).
Local Abbreviation NPv := (@AGj6.NPv n).
Local Abbreviation R8v := (@AGj6.R8v n).
Local Abbreviation N8D := (@AGj6.N8D n).
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Local Abbreviation PBv := (@AGj6.PBv ly n cl v).
Local Abbreviation Uv := (@AGj6.Uv ly cl v).
Local Abbreviation SUv := (@AGj6.SUv ly cl v).
Local Abbreviation FILv := (@AGj6.FILv n).
Local Abbreviation NDv := (@AGj6.NDv n).
Local Abbreviation XW := (@AGj6.XW ly n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E0 := (@AGj6.E0 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaT := (@AGj6.EaT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaC := (@AGj6.EaC ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSB := (@AGj6.EaSB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaTOP := (@AGj6.EaTOP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation Er := (@AGj6.Er ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E2 := (@AGj6.E2 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E1 := (@AGj6.E1 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E8 := (@AGj6.E8 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E10 := (@AGj6.E10 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation E4 := (@AGj6.E4 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaP := (@AGj6.EaP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaR8 := (@AGj6.EaR8 ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaK := (@AGj6.EaK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSK := (@AGj6.EaSK ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSSLOT := (@AGj6.EaSSLOT ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPB := (@AGj6.EaPB ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaPV := (@AGj6.EaPV ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaRZ := (@AGj6.EaRZ ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaU := (@AGj6.EaU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaSU := (@AGj6.EaSU ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaFIL := (@AGj6.EaFIL ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaNP := (@AGj6.EaNP ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation EaND := (@AGj6.EaND ly regs0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation WINT := (@AGj6.WINT ly cl).
Local Abbreviation PBW := (@AGj6.PBW ly n cl v).
Local Abbreviation WIN := (@AGj6.WIN ly regs0 n cl v).
Local Abbreviation win_in_WIN := (@AGj6.win_in_WIN ly regs0 n cl v).
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
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
(* The allocator instance (atom aINST = register 11 of the virtual regs0) lies in the image, below the depot. *)
Hypothesis Hinst : TFIB_IMG_LO <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 0xe60 <= 0x17c308.
Local Abbreviation HCdisj := (@AGj6.HCdisj _ ly regs0 tr v Hv LY Htrlen).
Local Abbreviation DZONE := (@AGj6.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation HC_NB := (@AGj6.HC_NB _ ly LY).
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Local Abbreviation HCX := (@AGj6.HCX _ ly LY).
Local Abbreviation tr_length := (@AGj6.tr_length tr Htrlen).
Local Abbreviation Kv_range := (@AGj6.Kv_range ly regs0 mem0 n tr cl v Hcl Hv Hv2 Htrlen DPOST).
Local Abbreviation high_facts := (@AGj6.high_facts _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation blocks_facts := (@AGj6.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AGj6.off_T _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_C := (@AGj6.off_C _ ly regs0 mem0 n tr v Hv LY IMG Htrlen DPOST).
Local Abbreviation off_NB := (@AGj6.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AGj6.off_SB _ ly LY IMG).
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Local Abbreviation K0_facts := (@AGj6.K0_facts n Nrange).
Local Abbreviation RZ_num := (@AGj6.RZ_num n Nrange).
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, AFSTACK, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Local Abbreviation derived_ranges := (@AGj6.derived_ranges _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Local Abbreviation CLk := (@AGj6.CLk).
Local Abbreviation CLk_E := (@AGj6.CLk_E ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Htrlen DPOST Nrange Hcl_def).
Local Abbreviation WIN1 := (@AGj6.WIN1 ly regs0 n cl v).
Local Abbreviation WIN1_WIN := (@AGj6.WIN1_WIN ly regs0 mem0 n tr cl v Htrlen DPOST).
Local Abbreviation WIN_odd := (@AGj6.WIN_odd ly regs0 mem0 n tr cl cnt v jb Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp Hinst DPOST Nrange).
Local Abbreviation WIN1_odd := (@AGj6.WIN1_odd ly regs0 mem0 n tr cl cnt v jb Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp Hinst DPOST Nrange).
Local Abbreviation WSKEL := (@AGj6.WSKEL).
Local Abbreviation WSKEL1 := (@AGj6.WSKEL1).
Local Abbreviation win_sub := (@AGj6.win_sub).
Local Abbreviation win_sub_sound := (@AGj6.win_sub_sound ly regs0 mem0 n tr v Hv Htrlen DPOST).
Local Abbreviation WSKEL_WIN := (@AGj6.WSKEL_WIN _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation WSKEL1_WIN1 := (@AGj6.WSKEL1_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation windows_WIN := (@AGj6.windows_WIN _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation windows_WIN1 := (@AGj6.windows_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation frame_WIN1 := (@AGj6.frame_WIN1 _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Htrlen DPOST Nrange).
Local Abbreviation WIN_not_high := (@AGj6.WIN_not_high _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Nrange).
Variables (mat0 : list word).
Let H0 := w_H W.
(* The registers at Allocate's entry, over the virtual regs0 of E0 (AGhy.REGS_G). *)
Variable regsU : bvmap 5 word.
Let cfg0 : config := mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEED : st_ok tfibsegs E0 KS_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Local Abbreviation all_disjoint_of_forall := (@AGj6.all_disjoint_of_forall).
Local Abbreviation kept_of_frame := (@AGj6.kept_of_frame W ly regs0 mem0 n tr v Htrlen DPOST).
Local Abbreviation SKEL_TAIL := (@AGj6.SKEL_TAIL).
Local Abbreviation stack_ivs := (@AGj6.stack_ivs _ ly regs0 mem0 n tr v Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation stack_ivs2 := (@AGj6.stack_ivs2 _ ly regs0 mem0 n tr v Hv LY Hsp Htrlen Hbp DPOST).
Local Abbreviation DZONE_disj := (@AGj6.DZONE_disj _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hso Hbp DPOST Nrange).
Local Abbreviation RFACTS := (@AGj6.RFACTS ly regs0 n cl v).
Local Abbreviation zone_lit := (@AGj6.zone_lit _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen DPOST Nrange).
Local Abbreviation zone_T := (@AGj6.zone_T _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Nrange).
Local Abbreviation zone_C := (@AGj6.zone_C _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Nrange).
Local Abbreviation zone_K := (@AGj6.zone_K _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp DPOST Nrange).
Local Abbreviation zone_SH := (@AGj6.zone_SH _ ly regs0 mem0 n tr cl cnt v Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen DPOST Nrange).
Local Abbreviation tail_ext_ok := (@AGj6.tail_ext_ok _ ly regs0 mem0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 Hcl Hv Hcnt Hv2 LY IMG Hsp Htrlen Hbp Hinst DPOST Nrange).
Local Abbreviation at_ST := (@AGj6.at_ST _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4).
Local Abbreviation at_ST2 := (@AGj6.at_ST2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_S2 := (@AGj6.at_S2 _ W ly regs0 mem0 md0 n tr cl cnt v csz j0 jb j1 j2 j3 j4 DPOST).
Local Abbreviation at_RET := (@AGj6.at_RET _ W ly regs0 mem0 md0 n cl cnt v jb DPOST).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Abbreviation memset_stretch := (@AGj6.memset_stretch _ W ly regs0 mem0 n tr cl cnt v jb Hcl Hv Hcnt Hjb Hsp Htrlen Hso Hbp Hinst DPOST Nrange).
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : PcapSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qmeter S.
Local Abbreviation case0_sizes := (@AGj6.case0_sizes n Nrange).
Local Abbreviation Kv_is_sptr := (@AGj6.Kv_is_sptr ly cl v Hcl B off Hoff_def).
Local Ltac addr_tac :=
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi];
rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, w64, ly_bot, kStackSpan, t_unwinding, t_cache, t_stats, TFIB_IMG_END, PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, UNW_STK, BST_SIZE, AFSTACK, IFRAME, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
rewrite ?unsigned_lit_small by zlia; zlia.
Local Ltac denot_tac :=
cbn [sv_denot]; rewrite ?EaT, ?EaC, ?EaTOP, ?EaSB, ?E2; unfold w64, ly_bot, kStackSpan in *;
first [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Zbv_add_unsigned; f_equal; zlia
| rewrite unsigned_lit_small by zlia; f_equal; zlia
| reflexivity ].
Hypothesis SEEDM : st_ok tfibsegs E0 MK_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Definition WINM (a : Z) : Prop := (sp0 - AFSTACK <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
(* The stack part is the scratch window below sp0; the second disjunct is empty (it kept the malloc interceptor's
   top-of-frame window) so that the shape of WINM1 is the released one. *)
Definition WINM1 (a : Z) : Prop :=
(sp0 - AFSTACK <= a < sp0) \/ (sp0 <= a < sp0) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Lemma WINM1_WINM : forall a, WINM1 a -> WINM a.
Proof. intros a H. unfold WINM1, WINM, AFSTACK in *. zlia. Qed.
Lemma WINM_WIN : forall a, WINM a -> WIN false a.
Proof. intros a H. unfold WINM, WIN, WINT in *. destruct H as [H|H]; [left; exact H | right; left; right; right; right; exact H]. Qed.
Definition WSKELM1 : list (option nat * Z * Z) := [(Some 2%nat, - AFSTACK, 0); (Some 2%nat, 0, 0); (Some 32%nat, t_unwinding, t_unwinding + 1)].
Lemma WSKELM1_WINM1 : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELM1 ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINM1 a.
Proof.
intros E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF'.
unfold WSKELM1 in Hin. cbn [In] in Hin. unfold WINM1.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV, IFRAME in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by zlia; rewrite ?E2, ?EaT in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by zlia;
unfold sp0 in *; zlia.
Qed.
Lemma windows_WINM1 : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINM1 a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELM1_WINM1 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. zlia.
Qed.
Lemma frame_WINM1 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELM1 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINM1 (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WINM1 E rs _ HE Hb Hw). Qed.
Definition at_STM (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINM (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0)).
Lemma at_STM_ST : forall ss W' c', at_STM ss W' c' -> at_ST ss W' c'.
Proof.
intros ss W' c' (HW & ms & mat & E' & Hc & HE & HS & HM & HP & HB). split; [exact HW|]. exists ms, mat, E'.
repeat (split; [assumption|]). split; [|split; assumption]. intros x Hx. apply HM. intros H. apply Hx. exact (WINM_WIN _ H).
Qed.
Ltac frame_accM HE :=
match goal with
| MEQ : (forall x : word, ~ WINM1 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINM1 (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WINM1 E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Local Ltac close_ST En HEn HS memB MEQ MEQW PRESW BUFW :=
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg ?msf (with_vm_backing _ ?matf _)] => exists msf, matf, En end;
split; [reflexivity|]; split; [exact HEn|]; split; [exact HS|];
pose proof derived_ranges as DR'; pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9); pose proof Kv_range as HKR;
pose proof (lo_top ly LY) as (T1' & T2' & T3' & T4' & T5' & T6' & T7'); pose proof Hsp as (Hlo_ & Hbot_ & Hhi_ & Hal_);
pose proof Hbp as (Hbp1_ & Hbp2_ & Hbp3_);
split; [|split];
[ intros x Hx; rewrite (MEQ x) by (intros H1; apply Hx, WINM1_WINM, H1); apply MEQW, Hx
| intros a Ha; eapply (st_ok_window_apresent_off (w_H W) En _ _ 1 _ a HS);
[reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn 2%nat (ltHAV 2 eq_refl)), E2; addr_tac | off_by ltac:(addr_tac) ]
| intros i Hi; pose proof tr_length as LEN;
eapply val_mem_frame; [|eapply val_mem_addr; [exact (BUFW i Hi) | clear - Hi LEN Hlo_ Hhi_ T4' T7'; addr_tac]];
intros k Hk; apply MEQ;
assert (Hx : ly_stk_lo ly <= BPv + 8 * Z.of_nat i + Z.of_nat k < ly_stk_hi ly) by (clear - Hi Hk LEN Hlo_ Hhi_ Hbp1_ Hbp2_; unfold AFSTACK in *; zlia);
destruct (F9 _ Hx) as [N1 N2]; pose proof (HCdisj _ Hx) as HC;
clear - Hi Hk LEN DR' HKR N1 N2 HC T7' T4' Hlo_ Hhi_ Hbp1_ Hbp2_ F1 F2 F3 F4 F5 F6 F7 F8;
unfold WINM1 in *; numconst; rewrite unsigned_lit_small by zlia; zlia ].
Lemma missA : SRr tfibsegs W cfg0 (at_STM MK_B).
Proof.
pose proof Hwx_tfa as Hwx. pose proof SEEDM as HS.
(* The walk starts at MK_1 (Allocate's entry): the scratch window below sp0 is region 1 of the seed and the
   trace is in the caller's buffer at BPv (PBUF0). *)
set (En1 := E0) in HS.
assert (HEn1 : forall k, (k < aHAV)%nat -> ew En1 k = ew E0 k) by (intros k Hk; reflexivity).
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
assert (MEQW : forall x : word, ~ WINM (bv_unsigned x) -> mem0 x = mem0 x) by (intros; reflexivity).
pose proof Hpres0 as PRESW. pose proof PBUF0 as BUFW.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn1.
pose proof K0_facts as (_ & NR & _ & _ & _ & R8r & R8m & _ & _ & _ & _ & _ & _ & _ & _ & _ & R8def).
assert (En10 : U En1 (SOff 10 0) = n).
{ clear - HEn1 Hn NR. rewrite U_zev by reflexivity. cbn [zev]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64.
rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_id. unfold M64. zlia. }
srr_branch_sh tfibtbl_rtA_ok HS.
2:{   rewrite branch_ltu_U, En10, (U_lit En1 8) in Hc by zlia. apply Z.ltb_ge in Hc.
srr_run_to_sh tfibtbl_rtA_ok HS 0x32688. frame_accM HEn1.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 Hc NR R8def. pin_zev. unfold aR8. rewrite (HEn1 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite R8def, Z.max_r by zlia. rewrite !zcanon_id by (unfold M64; zlia). reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MK_B in HS by (vm_compute; reflexivity) end.
close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW. }
rewrite branch_ltu_U, En10, (U_lit En1 8) in Hc by zlia. apply Z.ltb_lt in Hc.
assert (ZR8 : zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) = R8v).
{ clear - HEn1 Hn NR Hc R8def.
cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn1 10%nat (ltHAV 10 eq_refl)), E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (n + 7)) by (unfold M64; zlia). rewrite (zcanon_id 18446744073709551608) by (unfold M64; zlia).
change 18446744073709551608 with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite R8def, Z.max_l by zlia.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)). rewrite zcanon_id; unfold M64; zlia. }
srr_run_to_sh tfibtbl_rtA_ok HS 0x32688. frame_accM HEn1.
apply (st_ok_pin_regU _ _ _ 10%bv (SOff aR8 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 ZR8 R8r. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth]. unfold aR8.
change (zev (rho_of En1) (SOff 38 0) = zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En1) (SLit 0)))).
rewrite ZR8. cbn [zev zalu_raw]. unfold rho_of. rewrite (HEn1 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64.
rewrite unsigned_lit_small by zlia. zcanon_simp. zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (st_ok_pin_regU _ _ _ 11%bv (SLit 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn1 ZR8 R8r R8m. apply U_eq_by_zev; [reflexivity | reflexivity |]. cbn [sr_get ss_regs nth].
change (zev (rho_of En1) (SLit 0) = zcanon (zalu_raw 63 64 ALU_AND (zcanon (zalu_raw 63 64 ALU_ADD (zev (rho_of En1) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))) (zev (rho_of En1) (SLit 0)))) (zev (rho_of En1) (SLit 7)))).
rewrite ZR8. cbn [zev zalu_raw]. zcanon_simp. rewrite Z.add_0_r, land_7_mod by zlia. rewrite R8m. reflexivity. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MK_B in HS by (vm_compute; reflexivity) end.
close_ST En1 HEn1 HS mem0 MEQ MEQW PRESW BUFW.
Qed.
Lemma missB : forall W0 c, at_STM MK_B W0 c -> SRr tfibsegs W0 c (at_STM MK_E).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF.
pose proof K0_facts as (_ & NR & NPr & NP0 & NP1 & R8r & R8m & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_to_sh tfibtbl_rtA_ok HS 0x326a4. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aNP 0)) in HS. 2:{ intros X; discriminate. }
2:{ clear - HEn Hn NR NPr NP0 NP1. pin_zev. unfold aNP. rewrite (HEn 62%nat (ltHAV 62 eq_refl)), (HEn 10%nat (ltHAV 10 eq_refl)), EaNP, E10, Hn.
unfold w64. rewrite !unsigned_lit_small by zlia. rewrite (zcanon_id (n + 0)) by (unfold M64; zlia). rewrite (zcanon_id 1) by (unfold M64; zlia).
destruct (Z.ltb_spec (n + 0) 1);
[ rewrite (zcanon_id 1) by (unfold M64; zlia) | rewrite (zcanon_id 0) by (unfold M64; zlia) ]; rewrite !zcanon_id by (unfold M64; zlia); zlia. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
srr_branch_sh tfibtbl_rtA_ok HS.
2:{ exfalso. clear - Hc HEn R8r. rewrite branch_geu_U in Hc. apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc. revert Hc.
rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of, aR8.
rewrite (HEn 38%nat (ltHAV 38 eq_refl)), EaR8. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (R8v + 16)) by (unfold M64; zlia). change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by zlia.
zcanon_simp. zlia. }
clear Hc.
srr_run_to_sh tfibtbl_rtA_ok HS 0x36bb8. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 8%bv (SOff aCL 0)) in HS;
[ | intros X; discriminate
| lazymatch goal with |- U ?E _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
lazymatch goal with |- U ?E _ = U _ ?t => change t with CLk end;
apply U_eq_by_zev; [reflexivity | clear; vm_compute; reflexivity |]; rewrite (CLk_E En HEn);
cbn [zev]; unfold rho_of, aCL; rewrite (HEn 39%nat (ltHAV 39 eq_refl)), (eq_refl : ew E0 39 = w64 cl); unfold w64;
rewrite unsigned_lit_small by zlia; rewrite Z.add_0_r; apply zcanon_id; unfold M64; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
apply (YP03.st_ok_prune tfibsegs _ _ _ [] []) in HS.
lazymatch type of HS with st_ok _ _ ?ss _ => replace ss with MK_E in HS by (vm_compute; reflexivity) end.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma missC : forall W0 c, at_STM MK_E W0 c -> SRr tfibsegs W0 c (at_STM MK_CALL).
Proof.
intros W0 c (-> & ms & mat & En & -> & HEn & HS & MEQW & PRESW & BUFW). pose proof Hwx_tfa as Hwx.
pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof derived_ranges as DR. pose proof high_facts as LF. pose proof K0_facts as (_ & NR & NPr & _ & _ & R8r & R8m & NPR8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, t_unwinding in DR, LF.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) En _ _ HS eq_refl) as Hshape; cbn [ss_pc] in Hshape;
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape | _ => idtac end.
rewrite Hshape in HS. rewrite Hshape. set (mem1 := ms_mem ms) in *.
assert (MEQ : forall x : word, ~ WINM1 (bv_unsigned x) -> mem1 x = mem1 x) by (intros; reflexivity).
srr_run_sh tfibtbl_rtA_ok HS. frame_accM HEn.
apply (st_ok_pin_regU _ _ _ 9%bv (SOff aP 0)) in HS;
[ | intros X; discriminate
| clear - T SB HEn DR LF Hcl Hcnt Hv Hn; pin_zev; unfold aP;
rewrite (HEn 40%nat (ltHAV 40 eq_refl)), (HEn 32%nat (ltHAV 32 eq_refl)), (HEn 39%nat (ltHAV 39 eq_refl)), EaP, EaT, (eq_refl : ew E0 39 = w64 cl);
unfold w64; rewrite !unsigned_lit_small by (unfold Pv, t_cache in *; zlia); unfold Pv, t_cache in *; zcanon_simp; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts sr_set] in HS.
srr_run_to_sh tfibtbl_rtA_ok HS 0x37174. frame_accM HEn.
close_ST En HEn HS mem1 MEQ MEQW PRESW BUFW.
Qed.
Lemma miss1 : SRr tfibsegs W cfg0 (at_STM MK_CALL).
Proof.
eapply SRr_bind; [exact missA|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (missB W1 c1 H1)|]. intros W2 c2 _ H2. exact (missC W2 c2 H2).
Qed.
End e.
End d.
