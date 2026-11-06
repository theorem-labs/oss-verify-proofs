(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjt.v (a working branch 30a1993588f, c5 + memnorm; file sha256 647da1c93656) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 17 image addresses moved by code-verified function pairs (17 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 1 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AGif2.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AB1q AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09 YG0b YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGid AGie AGif.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGjv AGjw AGjx AGjh AGjn AGjo AGjk AGjl AGjp AGjs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AFia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section g.
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
Local Abbreviation SHBv := (@AGjm.SHBv).
Local Abbreviation QSv := (@AGjm.QSv ly idx).
Local Abbreviation Kv := (@AGjm.Kv mb).
Local Abbreviation Uv := (@AGjm.Uv mb).
Local Abbreviation ENDv := (@AGjm.ENDv n mb).
Local Abbreviation TLv := (@AGjm.TLv n).
Local Abbreviation UEv := (@AGjm.UEv n mb).
Local Abbreviation RLv := (@AGjm.RLv n).
Local Abbreviation SMv := (@AGjm.SMv mb).
Local Abbreviation PBv := (@AGjm.PBv n mb).
Local Abbreviation LGv := (@AGjm.LGv n).
Local Abbreviation BSLv := (@AGjm.BSLv regs0 n).
Local Abbreviation XW := (@AGjm.XW ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E0 := (@AGjm.E0 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Er := (@AGjm.Er ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@AGjm.E1 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@AGjm.E2 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E4 := (@AGjm.E4 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E8 := (@AGjm.E8 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@AGjm.E10 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@AGjm.EaT ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@AGjm.EaC ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@AGjm.EaSB ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@AGjm.EaTOP ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaR8 := (@AGjm.EaR8 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
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
Hypothesis Hinst : 0x9d000 <= INSTv /\ INSTv + 0xe60 <= 0x128320 /\ INSTv mod 8 = 0.
Hypothesis Nrange : 64513 <= n < SEC_NMAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@AGjm.mod0_of_mul).
Local Abbreviation size_facts := (@AGjm.size_facts n Nrange).
Local Abbreviation tr_length := (@AGjm.tr_length tr Htrlen).
Local Abbreviation high_facts := (@AGjm.high_facts _ ly regs0 tr idx res LY IMG Htrlen Hinst Hidx Hres).
Local Abbreviation stack_ivs := (@AGjm.stack_ivs _ ly regs0 tr idx res LY Hsp Htrlen Hbp Hinst Hidx Hres).
Local Abbreviation HCX := (@AGjm.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
(* The stack object at aSO holds the buffer pointer and the trace length. *)
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem0) SOv 8 BPv.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem0) (SOv + 8) 8 (Z.of_nat (length tr)).
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@AGjm.map_facts _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@AGjm.map_zone _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@AGjm.map_zoneN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@AGjm.map_in_band _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@AGjm.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@AGjm.WINT ly).
Local Abbreviation WINI := (@AGjm.WINI regs0 n).
Local Abbreviation WINM := (@AGjm.WINM ly n idx mb).
Local Abbreviation WIN := (@AGjm.WIN ly regs0 n idx mb).
Local Abbreviation WINN := (@AGjm.WINN ly regs0).
Local Abbreviation WINP := (@AGjm.WINP ly regs0 n).
Local Abbreviation WINP_WIN := (@AGjm.WINP_WIN ly regs0 n idx mb).
Local Abbreviation WIN1P := (@AGjm.WIN1P ly regs0 n).
Local Abbreviation WIN1 := (@AGjm.WIN1 ly regs0 n idx mb).
Local Abbreviation WIN1P_WINP := (@AGjm.WIN1P_WINP ly regs0 n tr idx res mb Htrlen Hidx).
Local Abbreviation WIN1_WIN := (@AGjm.WIN1_WIN ly regs0 n tr idx res mb Htrlen Hidx).
Local Abbreviation WIN1P_WIN1 := (@AGjm.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@AGjm.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx).
Local Abbreviation WSKELP := (@AGjm.WSKELP).
Local Abbreviation WSKEL1P := (@AGjm.WSKEL1P).
Local Abbreviation WMAP := (@AGjm.WMAP).
Local Abbreviation WSKEL := (@AGjm.WSKEL).
Local Abbreviation WSKEL1 := (@AGjm.WSKEL1).
Local Abbreviation win_sub := (@AGjm.win_sub).
Local Abbreviation win_sub_sound := (@AGjm.win_sub_sound ly regs0 tr idx res mb Htrlen Hinst Hidx Hres).
Local Abbreviation in_win := (@AGjm.in_win).
Local Abbreviation WSKELP_WINP := (@AGjm.WSKELP_WINP _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@AGjm.WSKEL1P_WIN1P _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@AGjm.WMAP_WINM _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@AGjm.WSKEL_WIN _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@AGjm.WSKEL1_WIN1 _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@AGjm.windows_in ly regs0 tr idx res mb Htrlen Hinst Hidx Hres).
Local Abbreviation windows_WINP := (@AGjm.windows_WINP _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@AGjm.windows_WIN1P _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@AGjm.windows_WIN _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@AGjm.windows_WIN1 _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@AGjm.frame_WIN1P _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@AGjm.frame_WIN1 _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@AGjm.WINP_not_high _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@AGjm.WIN_not_high _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
(* The registers at Allocate's entry, over the virtual regs0 of E0 (AGhy.REGS_G). *)
Variable regsU : bvmap 5 word.
Let cfg0 : config := mkCfg (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
(* The walk starts at S_1 (Allocate's entry): the scratch window below sp0 is a region of the seed and the
   trace is in the caller's buffer at BPv (PBUF0). *)
Hypothesis SEED : st_ok tfibsegs E0 S_1 (restrict (w_H W) (mkst regsU (w64 A_Allocate) mem0 (seg_rom tfibsegs))).
Hypothesis PBUF0 : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem0) (BPv + 8 * Z.of_nat i) 8 (nth i tr 0).
Local Abbreviation all_disjoint_of_forall := (@AGjm.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@AGjm.img_rw_writable ly regs0 tr idx res mb Htrlen Hidx).
Local Abbreviation kept_of_frame := (@AGjm.kept_of_frame W ly regs0 tr idx res mb Htrlen Hidx).
Local Abbreviation SKEL_TAIL := (@AGjm.SKEL_TAIL).
Local Abbreviation blocks_facts := (@AGjm.blocks_facts _ ly LY IMG).
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
Local Abbreviation DZONE_disj := (@AGjm.DZONE_disj _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@AGjm.RFACTS ly regs0).
Local Abbreviation zone_lit := (@AGjm.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@AGjm.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@AGjm.zone_T _ ly regs0 tr idx res LY IMG Hsp Htrlen Hbp Hinst Hidx Hres).
Local Abbreviation zone_C := (@AGjm.zone_C _ ly regs0 tr idx res LY IMG Hsp Htrlen Hbp Hinst Hidx Hres).
Local Abbreviation tail_ext_ok := (@AGjm.tail_ext_ok _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@AGjm.RFACTS_map _ ly regs0 n tr idx res mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@AGjm.at_ST _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@AGjm.memset_stretch _ _ W ly regs0 mem0 n tr idx res mb Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Local Abbreviation at_S := (@AGjm.at_S _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@AGjm.at_N _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@AGjm.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@AGjm.pstable).
Local Abbreviation stack_shaped := (@AGjm.stack_shaped).
Local Abbreviation window_present := (@AGjm.window_present ly regs0 tr idx res Htrlen Hidx).
Local Abbreviation stack_present_of := (@AGjm.stack_present_of _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hidx).
Local Abbreviation wins_ok := (@AGjm.wins_ok).
Local Abbreviation at_S_run_gen := (@AGjm.at_S_run_gen _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hidx).
Local Abbreviation at_S_run_ecall_gen := (@AGjm.at_S_run_ecall_gen _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hidx).
Local Abbreviation at_S_runP := (@AGjm.at_S_runP _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@AGjm.at_S_runM _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@AGjm.at_S_run_ecallP _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@AGjm.at_S_run_ecallM _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@AGjm.at_S_pin _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@AGjm.at_S_arm _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@AGjm.at_S_forget _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@AGjm.at_S_noconds _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_weaken := (@AGjm.at_S_weaken _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts := (@AGjm.at_S_facts _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_strengthen := (@AGjm.at_S_strengthen _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@AGjm.at_S_eq _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_open := (@AGjm.at_S_open _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation CSAVEDS := (@AGjm.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@AGjm.sv_denot_SOff0).
Local Abbreviation at_S_ret := (@AGjm.at_S_ret _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@AGjm.kept_of_frame2 ly regs0 tr idx res Htrlen Hidx).
Local Abbreviation at_N_cont := (@AGjm.at_N_cont _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hidx).
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
(* The machine facts of the secondary path over the instance at INSTv (no allocator model). *)
Hypothesis SV : AGif2.sview B W ly INSTv mem0 idx res.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
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
Local Abbreviation vis_present := (@AGjv.vis_present _ W ly regs0 mem0 tr idx res Htrlen Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@AGjv.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@AGjv.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@AGjv.in_as_junk ly B S).
Local Abbreviation junk_word := (@AGjv.junk_word _ W ly regs0 mem0 tr idx res LY IMG Htrlen Hinst Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@AGjv.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AGjv.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AGjv.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_sec := (@AGjv.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@AGjv.sec_vals _ W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@AGjv.unwinding_val _ W ly mem0 B S HARm).
Local Abbreviation rw_writable := (@AGjv.rw_writable ly regs0 tr idx res Htrlen Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@AGjv.val_mem_mod8 W ly regs0 mem0 tr idx res Htrlen Hidx DPOST S).
Local Abbreviation chunk_lit := (@AGjv.chunk_lit W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@AGjv.chunk_lit_at W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@AGjv.chunk_atom W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htrlen Hidx DPOST S).
Local Abbreviation SREG0_ok := (@AGjw.SREG0_ok _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hpres0 PSO PLEN DPOST B TS SV Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PAIRS_ok := (@AGjx.PAIRS_ok _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@AGjx.FACTS_ok _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (@AGjx.SEED_ok _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PBUF := (@AGjh.PBUF W regs0 tr).
Local Abbreviation PBUF_stableP := (@AGjh.PBUF_stableP _ W ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@AGjh.PBUF_stableM _ W ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap).
Local Abbreviation seg0 := (@AGjh.seg0 _ W ly regs0 mem0 md0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hpres0 mat0 regsU SEED PBUF0).
Local Abbreviation appregs := (@AGjn.appregs).
Local Abbreviation st_ok_appregs := (@AGjn.st_ok_appregs _).
Local Abbreviation at_S_app := (@AGjn.at_S_app _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@AGjn.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@AGjn.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@AGjn.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@AGjn.WIN1N_WINPN ly regs0 n tr idx res mb Htrlen Hidx).
Local Abbreviation windows_WIN1N := (@AGjn.windows_WIN1N _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation buf_not_WIN1N := (@AGjn.buf_not_WIN1N _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@AGjn.at_S_runN _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@AGjn.PBUF_stableN _ W ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres).
Local Abbreviation at_S_val := (@AGjn.at_S_val _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@AGjn.memset_stretchW _ W ly regs0 mem0 n tr idx res Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@AGjn.at_S_memset _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@AGjn.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@AGjn.WIN1T_WIN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@AGjn.windows_WIN1T _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@AGjn.WIN1T_WIN1_aux _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation buf_not_WIN1T := (@AGjn.buf_not_WIN1T _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@AGjn.at_S_runT _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@AGjn.at_S_run_ecallT _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@AGjn.PBUFW regs0 tr).
Local Abbreviation PBUFW_stableT := (@AGjn.PBUFW_stableT _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@AGjo.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@AGjo.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@AGjo.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@AGjo.WIN1S_WIN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@AGjo.windows_WIN1S _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation buf_not_WIN1S := (@AGjo.buf_not_WIN1S _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@AGjo.at_S_runS _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@AGjo.at_S_run_ecallS _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@AGjo.brun).
Local Abbreviation run_ok := (@AGjo.run_ok n mb).
Local Abbreviation PS := (@AGjo.PS regs0 n tr mb).
Local Abbreviation runs_not_WIN1S := (@AGjo.runs_not_WIN1S _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@AGjo.runs_not_stack _ ly regs0 n tr idx res mb LY Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@AGjo.PS_stable _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@AGjo.cut1).
Local Abbreviation cut := (@AGjo.cut).
Local Abbreviation cut_sound := (@AGjo.cut_sound _ ly regs0 mem0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@AGjo.cut_ok ly regs0 mem0 n tr idx res mb Htrlen Hinst Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@AGjo.at_S_memsetS _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@AGjo.skel_okb).
Local Abbreviation skel_cases := (@AGjo.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@AGjo.skel_apart _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@AGjo.skel_u64 _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hinst Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@AGjo.memset_ext_of_skel _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@AGjo.memset_u64_of_skel _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hinst Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@AGjo.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@AGjo.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@AGjo.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@AGjo.WIN1R_WIN _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@AGjo.windows_WIN1R _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation buf_not_WIN1R := (@AGjo.buf_not_WIN1R _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@AGjo.at_S_runR _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@AGjo.at_S_run_ecallR _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@AGjo.PSR regs0 n tr mb).
Local Abbreviation rstable := (@AGjo.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@AGjo.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@AGjo.PSR_stable _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@AGjo.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@AGjo.QS_not_WIN1R _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@AGjo.QSP_rstable _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@AGjo.at_S_memsetSR _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@AGjo.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@AGjo.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@AGjo.subregionb).
Local Abbreviation subregionb_sound := (@AGjo.subregionb_sound ly regs0 mem0 tr idx res Htrlen Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@AGjo.submemb).
Local Abbreviation submemb_sound := (@AGjo.submemb_sound ly regs0 mem0 tr idx res Htrlen Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@AGjo.at_S_submem _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htrlen Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@AGjo.at_S_addreg _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@AGjk.PSR_runs _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@AGjk.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@AGjk.SH0 n mb).
Local Abbreviation SH1 := (@AGjk.SH1 n mb).
Local Abbreviation SH2 := (@AGjk.SH2 n mb).
Local Abbreviation SH_ok := (@AGjk.SH_ok _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@AGjk.segG1 _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RX_stableS := (@AGjl.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@AGjl.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@AGjl.pstable_and).
Local Abbreviation PSR_stableS' := (@AGjl.PSR_stableS' _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@AGjl.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@AGjl.at_S_setchunks _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@AGjl.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@AGjl.RES2T_ne ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@AGjl.RES2T_eq ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@AGjl.sv_denot_eq_of_U ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@AGjl.skel_apart_QS _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@AGjl.QSPX ly idx).
Local Abbreviation segNE := (@AGjl.segNE _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@AGjl.segEQa _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@AGjl.zev_SAlu).
Local Abbreviation zev_SLit := (@AGjl.zev_SLit).
Local Abbreviation zev_SOff := (@AGjl.zev_SOff).
Local Abbreviation segJ2 := (@AGjl.segJ2 _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@AGjl.segJ _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@AGjp.QR ly res).
Local Abbreviation segT1 := (@AGjp.segT1 _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@AGjp.DX ly regs0).
Local Abbreviation PD := (@AGjp.PD ly mem0 DPOST).
Local Abbreviation PD_rstable := (@AGjp.PD_rstable _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PD_stableT := (@AGjp.PD_stableT _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PSR_stableS := (@AGjp.PSR_stableS _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@AGjp.PD_stableS _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX := (@AGjp.PDX ly mem0 DPOST).
Local Abbreviation PDX_rstable := (@AGjp.PDX_rstable _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableT := (@AGjp.PDX_stableT _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableS := (@AGjp.PDX_stableS _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation dx_okb := (@AGjp.dx_okb).
Local Abbreviation skel_apart_DX := (@AGjp.skel_apart_DX _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@AGjp.skel_apart_stk _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@AGjp.at_S_depot _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH3 := (@AGjp.SH3 n mb).
Local Abbreviation SH4 := (@AGjp.SH4 n mb).
Local Abbreviation shadow_marks := (@AGjp.shadow_marks _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@AGjp.SH34_ok _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@AGjp.segT2b _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@AGjp.segT2 _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SHLO := (@AGjs.SHLO).
Local Abbreviation SHHI := (@AGjs.SHHI n).
Local Abbreviation SH_hull := (@AGjs.SH_hull ly regs0 n tr res Htrlen Hinst Nrange S).
Local Abbreviation lit_m1 := (@AGjs.lit_m1).
Local Abbreviation lit_enomem := (@AGjs.lit_enomem).
Local Abbreviation nores34 := (@AGjs.nores34).
Local Abbreviation core34 := (@AGjs.core34).
Local Abbreviation pru_MS := (@AGjs.pru_MS ly regs0 n tr res Htrlen Nrange S).
Local Abbreviation grant_anon_shape := (@AGjs.grant_anon_shape).
Local Abbreviation Hcut_out := (@AGjs.Hcut_out).
Local Abbreviation S_N_facts := (@AGjs.S_N_facts).
Local Abbreviation S_N_ext64 := (@AGjs.S_N_ext64 _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres S).
Local Abbreviation S_N_win64 := (@AGjs.S_N_win64 _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres S).
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
RUN HR tbl tblok 0x55214 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5506c Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x55214 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x55254 Sh3 HX HP;
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
RUN HR tbl tblok 0x55214 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5506c Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x55214 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x55250 Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x55254 Sh3 HX HP;
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
RUN HR tbl tblok 0x320f8 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x320fc Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Variables (Wy : world tfibsegs) (md1 : Model).
Definition S_VG : sstate := Eval vm_compute in mkSS 0x65a0c (ss_regs S_V) (ss_mem S_V) None (ss_facts S_V).
Definition TQ : sv := SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_ADD (SOff aQ 0) (SAlu ALU_SLL (SOff aNCH 0) (SLit 3))) (SLit 18446744073709547520)) (SLit 0).
Lemma S_V_facts : ss_pc S_V = 0x65a08 /\ sr_get (ss_regs S_V) 17%bv = SLit 222 /\ sr_get (ss_regs S_V) 10%bv = TQ /\ sr_get (ss_regs S_V) 11%bv = SLit 131072 /\
sr_get (ss_regs S_V) 12%bv = SLit 3 /\ sr_get (ss_regs S_V) 13%bv = SLit 50 /\ sr_get (ss_regs S_V) 14%bv = SLit 18446744073709551615 /\ sr_get (ss_regs S_V) 15%bv = SLit 0 /\
no_cdata (ss_mem S_V) = true /\ resume S_V TQ (ss_mem S_V) (ss_facts S_V) = S_VG /\ sv_atoms_lt sHAV TQ = true.
Proof. clear. vm_compute. repeat split; reflexivity. Qed.
Definition ZQF (Wz : world tfibsegs) (m : word -> option byte) : Prop :=
forall a, QR a -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Definition ZQ (Wz : world tfibsegs) (m : word -> option byte) : Prop :=
idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> w_H Wz (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
Lemma QR_facts : idx = res -> QSv = Qb + 8 * res /\ QSv mod 131072 = Qb mod 131072 /\ QSv mod 4096 = 0 /\ (4096 <= Qb <= QSv /\ zone3cases Qb kPtrArrayResv) /\ QSv + 131072 <= Qb + kPtrArrayResv /\
Qb + kPtrArrayResv <= ASAN_CEIL /\ (forall a, QR a <-> QSv <= a < QSv + 131072).
Proof.
intros Heq. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _). pose proof Hidx as HI. pose proof Hres as [HRS HRM].
unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. unfold page_aligned in F11. unfold zone3 in F9.
assert (E1 : QSv = Qb + 8 * res) by (unfold QSv; try unfold Qb; rewrite Heq; reflexivity).
apply Z.mod_divide in HRM as [q Hq]; [|zlia]. apply Z.mod_divide in F11 as [p Hp]; [|zlia].
split; [exact E1|]. split. { rewrite E1, Hq. replace (Qb + 8 * (q * 16384)) with (Qb + q * 131072) by zlia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by zlia. reflexivity. }
split. { rewrite E1, Hq. try unfold Qb in *. rewrite Hp. replace (p * 4096 + 8 * (q * 16384)) with ((p + q * 32) * 4096) by zlia. apply Z_mod_mult. }
split; [split; [rewrite E1; zlia | exact (proj2 (proj2 F9))]|]. split; [rewrite E1; unfold kPtrArrayResv; zlia|]. split; [exact F10|].
intros a. unfold QR. rewrite E1. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv. zlia.
Qed.
Lemma ZQ_of_ZQF : forall Wz m, ZQF Wz m -> ZQ Wz m.
Proof. clearP. intros Wz m H _ a Ha _. exact (H a Ha). Qed.
Lemma QR_not_WIN1T : idx = res -> forall a, QR a -> ~ (QSv <= a < QSv + 8) -> ~ WIN1T a.
Proof.
intros Heq a Ha Hs Hw. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ). apply EQ in Ha.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _ & _ & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & Z4 & _ & _ & _ & Z8 & _).
pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof Nrange as NR. pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _). pose proof size_facts as (_ & _ & Z3 & Z4' & _).
assert (D1 : N8D / 8 <= R8v / 8) by (apply Z.div_le_mono; clear - Z3 Z4' MZ; zlia).
pose proof Hidx as HI. pose proof Hres as [HRS _]. unfold kMaxNumChunks in HI, HRS.
unfold WIN1T in Hw. clear EQ. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
- unfold WIN1P, WINT, WINI in Hw. clear - Ha Hw Q5 F9 F10 SC S1 QT HB E1 Heq HI HRS MZ Hinst.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kThreadObjSize, AFSTACK, IFRAME, t_unwinding, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *.
try unfold T in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- exact (Hs Hw).
- clear - Ha Hw MQ Z8 Q5 E1 Heq HI HRS MZ. unfold kPtrArrayResv, SEC_NMAX in *. try unfold Qb in *. zlia.
- clear - Ha Hw PB A2 A3 A6 SM2 D1 F9 Q5 E1 Heq HI HRS MZ Z4. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kPtrArrayResv in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableT : forall Wz, pstable WIN1T (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia). exact (QR_not_WIN1T Heq a Ha Hs).
Qed.
Lemma ZQ_rstable : forall Wz, rstable (ZQ Wz).
Proof.
intros Wz. split.
- intros m m' FR. apply (ZQ_stableT Wz m m'). intros x Hx. apply FR. intros Hw. exact (Hx (WIN1S_WIN1T _ (WIN1R_WIN1S _ Hw))).
- intros m m' d len Hp FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Lemma ZQ_stableD : forall Wz, pstable DX (ZQ Wz).
Proof.
intros Wz m m' FR H Heq a Ha Hs. destruct (H Heq a Ha Hs) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|].
pose proof (QR_facts Heq) as (_ & _ & _ & F9 & Q5 & F10 & EQ). pose proof (proj1 (EQ a) Ha) as Ra.
rewrite unsigned_lit_small by (clear - Ra F9 F10 Q5; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
intros [Hd|Hd]; revert Hd; clear - Ra F9 F10 Q5 QNB QSB S1 S3 SC; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, DEP_STK, AFSTACK, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in *; try unfold Qb in *; try unfold sp0 in *; zlia.
Qed.
Lemma skel_apart_Q : forall (E' : env) r, env_agree sHAV E0 E' -> skel_okb false (skel r) = true -> YP09.r_base r <> Some aQS ->
base_val E' (YP09.r_base r) + YP09.r_hi r <= Qb \/ Qb + kPtrArrayResv <= base_val E' (YP09.r_base r) + YP09.r_lo r \/ YP09.r_hi r <= YP09.r_lo r.
Proof.
intros E' r [HE _] Hs Hnq. destruct r as [b lo hi wlo whi cs]. unfold skel in Hs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _ & _ & _ & _ & F15).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof BSLv_range as HB.
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_stk_ceil ly LY) as SC.
destruct Hmap_apart as (_ & _ & _ & MQ & _). pose proof HCX as (_ & _ & QT & CQ). unfold zdisjoint in MQ, QT, CQ. cbn [fst snd] in MQ, QT, CQ.
pose proof (u64_range (getr regs0 2)) as U2.
destruct (skel_cases false b lo hi wlo whi Hs) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]]]; cbn [base_val].
- clear - A1 A2 F9 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
- rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2. clear - A1 A2 S1 SC F10 U2 MZ. ceil; unfold AFSTACK, ASAN_CEIL in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- rewrite (HE 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - A1 A2 QT MZ. unfold kThreadObjSize in *. try unfold T in *. try unfold Qb in *. zlia.
- rewrite (HE 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - A1 A2 CQ MZ. try unfold Qb in *. zlia.
- unfold aMAP. rewrite (HE 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
clear - A1 A2 MQ Z8 MZ. unfold SEC_NMAX in *. try unfold Qb in *. zlia.
- exfalso. apply Hnq. reflexivity.
- unfold aBSL. rewrite (HE 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB MZ Hinst; zlia).
clear - A1 A2 HB F9 MZ Hinst. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
- unfold aINST. rewrite (HE 11%nat ltac:(unfold sHAV; zlia)), E11.
clear - A1 A2 F9 MZ Hinst. unfold INSTv, zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. try unfold Qb in *. zlia.
- unfold aSO. rewrite (HE 13%nat ltac:(unfold sHAV; zlia)), E13. pose proof Hso as (O1 & O2 & _).
clear - A1 A2 O1 S1 SC F10 MZ. ceil; unfold AFSTACK, ASAN_CEIL, SOv, sp0 in *. try unfold Qb in *. zlia.
- discriminate Epb.
Qed.
Lemma TQ_val : idx = res -> U E0 TQ = QSv.
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kMaxNumChunks, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *.
assert (HQb : 0 <= Qb /\ Qb + 8388608 <= 140737479966720) by (clear - F9 F10; zlia).
clear - Heq E1 QA Q5 HI HRS HQb.
unfold TQ. rewrite U_zev by reflexivity. cbn [zev zalu_raw zmd_raw]. unfold rho_of. unfold_atoms. rewrite EaQ, EaNCH. unfold w64.
try unfold Qb in *. rewrite !unsigned_lit_small by (clear - HI HQb; zlia).
rewrite !Z.add_0_r. rewrite (zcanon_id idx) by (unfold M64; clear - HI; zlia). change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by (clear; zlia). change (2 ^ 3) with 8.
rewrite (zcanon_id (idx * 8)) by (unfold M64; clear - HI; zlia). rewrite (zcanon_id (ly_Q ly)) by (unfold M64; clear - HQb; zlia).
rewrite (zcanon_id (ly_Q ly + idx * 8)) by (unfold M64; clear - HI HQb; zlia). change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by (clear - HI HQb; zlia). change (2 ^ 12) with 4096.
assert (MZ : (ly_Q ly + idx * 8) mod 4096 = 0) by (rewrite Heq, (Z.mul_comm res 8), <- E1; exact QA).
rewrite MZ, Z.sub_0_r. rewrite (zcanon_id (ly_Q ly + idx * 8)) by (unfold M64; clear - HI HQb; zlia). rewrite zcanon_id by (unfold M64; clear - HI HQb; zlia). rewrite E1, Heq. zlia.
Qed.
Lemma nores50 : mmap_noreserve_b (Z_to_bv 64 50) = false. Proof. clear. reflexivity. Qed.
Lemma core50 : mmap_flags_core (Z_to_bv 64 50) = 50. Proof. clear. reflexivity. Qed.
Lemma pru17 : page_round_up_Z 131072 = 131072. Proof. clear. reflexivity. Qed.
Lemma grant_piece_shape : forall (a k : word) md, let md' := grant_md false (Z_to_bv 64 50) a k md in
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md).
Proof.
clear. intros a k md. cbv zeta. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm sg sc]. cbn. destruct maps; cbn. repeat split; reflexivity.
Qed.
Lemma nodeV : forall {RT : Type} (sN : astate) (K : Z -> itree astate RT) (Q : RT -> world tfibsegs -> config -> Prop)
(R : (word -> option byte) -> Prop) (c1 : config),
idx = res ->
at_N Wy md1 WIN (PSR Wy SH2 R) S_V Wy c1 -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) ->
(forall m m' : word -> option byte, (forall x : word, ~ QR (bv_unsigned x) -> m' x = m x) -> R m -> R m') ->
amwf (cfg_model c1) ->
vm_reserved (m_vmmaps (cfg_model c1)) = segments_reserved tfibsegs ->
(forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
In (wiv (Qb, kPtrArrayResv)) (vm_maps (m_vmmaps (cfg_model c1))) ->
eager_used (cfg_model c1) + A_bytes (w_A Wy) + 2 ^ 19 <= vm_limit (m_vmmaps (cfg_model c1)) ->
YM05.ceil_of_top (alloc_top (m_vmmaps (cfg_model c1))) ->
(forall z, z = 0 \/ z = 1 -> aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) z) ->
(forall (W5 : world tfibsegs) (c' : config), let md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) (cfg_model c1) in
wle Wy W5 -> hsub (w_H W5) (w_H Wy) -> (forall x : word, w_H Wy x = false -> w_H W5 x = false) ->
w_A W5 = (QSv, QSv + 131072) :: w_A Wy ->
(forall x : word, QSv <= bv_unsigned x < QSv + 131072 -> w_H W5 x = false) ->
(forall x : word, ~ (QSv <= bv_unsigned x < QSv + 131072) -> w_H W5 x = w_H Wy x) ->
AI tfibsegs (w_H W5) (w_A W5) md5 -> amwf md5 -> same_io md0 md5 -> eager_used md5 <= eager_used (cfg_model c1) + 131072 ->
vm_maps (m_vmmaps md5) = vm_maps (m_vmmaps (cfg_model c1)) /\ vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps (cfg_model c1)) /\
vm_limit (m_vmmaps md5) = vm_limit (m_vmmaps (cfg_model c1)) /\ vm_mmap_base (m_vmmaps md5) = vm_mmap_base (m_vmmaps (cfg_model c1)) ->
at_S W5 md5 (fun a => WIN a \/ QR a) (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_VG W5 c' ->
amreal tfibsegs (K 1) W5 c' Q) ->
same_io md0 (cfg_model c1) ->
exists (I : Type) (nx : I -> config) (bit : I -> Z) (sp : I -> bool) (i0 : I),
node_ok tfibsegs c1 I (fun _ => []) nx /\
(forall i, AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model c1) -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i))) /\
(forall i, aok sN (KMapPtrArray (8 * idx) kPtrArrayCommit) (bit i)) /\ sp i0 = false /\ bit i0 = 1 /\
(forall i, sp i = false -> bit i = 1) /\
(forall i, sp i = true -> AI tfibsegs (w_H Wy) (w_A Wy) (cfg_model (nx i)) -> srealizes tfibsegs (nx i) t_nil) /\
(forall i, sp i = false -> amreal tfibsegs (K (bit i)) Wy (nx i) Q).
Proof.
intros RT sN K Q R c1 Heq HN HAI RQ MW RSV IMGS INQ SL0 HTOP Haok GRANT IO0.
pose proof (QR_facts Heq) as (E1 & _ & QA & F9 & Q5 & F10 & EQR).
destruct HN as (_ & ms & mat & E' & Ec & HE & HS & Hrv & MEQ & PRS & HPm).
set (mdN := with_vm_backing (m_vm_lazy md1) mat md1) in *.
assert (EcM : cfg_model c1 = mdN) by (rewrite Ec; reflexivity). rewrite EcM in *.
assert (MWF0 : MWF mdN) by (apply (proj1 (amwf_MWF mdN)); exact (proj1 MW)).
destruct (st_ok_ecall_shape_r tfibsegs (w_H Wy) E' S_V ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (HEn : forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) by (exact (proj1 HE)).
pose proof S_V_facts as (Hpc & H17 & H10 & H11 & H12 & H13 & H14 & H15 & Hnc & Hres_g & Hatq).
assert (UQS : bv_unsigned (w64 QSv) = QSv) by (unfold w64; apply unsigned_lit_small; clear - F9 F10 Q5 E1; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
assert (Un : bv_unsigned (w64 131072) = 131072) by (unfold w64; apply unsigned_lit_small; clear; zlia).
assert (R17 : getr regs 17 = Z_to_bv 64 222) by (rewrite (Hregs 17%bv), H17; reflexivity).
assert (R10 : getr regs 10 = w64 QSv).
{ rewrite (Hregs 10%bv), H10. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E' TQ)). f_equal.
change (bv_unsigned (sv_denot E' TQ)) with (U E' TQ). rewrite (U_agree sHAV E0 E' TQ HE Hatq). exact (TQ_val Heq). }
assert (R11 : getr regs 11 = Z_to_bv 64 131072) by (rewrite (Hregs 11%bv), H11; reflexivity).
assert (R12 : getr regs 12 = Z_to_bv 64 3) by (rewrite (Hregs 12%bv), H12; reflexivity).
assert (R13 : getr regs 13 = Z_to_bv 64 50) by (rewrite (Hregs 13%bv), H13; reflexivity).
assert (R14 : getr regs 14 = Z_to_bv 64 (-1)) by (rewrite (Hregs 14%bv), H14; cbn [sv_denot]; apply lit_m1).
assert (R15 : getr regs 15 = Z_to_bv 64 0) by (rewrite (Hregs 15%bv), H15; reflexivity).
assert (CEIL : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_ceiling).
{ rewrite UQS, pru17. clear - Q5 F10. ceil; unfold ASAN_CEIL, kPtrArrayResv in *. zlia. }
assert (CEILT : bv_unsigned (w64 QSv) + page_round_up_Z 131072 <= alloc_top (m_vmmaps mdN)).
{ eapply Z.le_trans; [exact CEIL | apply YM05.ceil_le_top; exact HTOP]. }
assert (PLACE : region_free (vm_reserved (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true /\
map_contains (vm_maps (m_vmmaps mdN)) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) = true).
{ rewrite pru17. split.
- rewrite RSV. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9z & _).
apply (tfib_region_free_reserved QSv 131072); [clear; zlia | clear - F9 F10 Q5 E1; ceil; unfold ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia |].
clear - F9z F9 Q5 E1. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- apply (YA09.map_contains_intro _ (w64 QSv) (w64 131072) (w64 Qb) (w64 kPtrArrayResv) INQ);
unfold w64; rewrite !unsigned_lit_small by (clear - F9 F10 Q5 E1; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia);
clear - Q5 E1 Heq F9; unfold kPtrArrayResv in *; try unfold Qb in *; zlia. }
assert (SL1 : eager_used mdN + A_bytes (w_A Wy) + page_round_up_Z 131072 <= vm_limit (m_vmmaps mdN)) by (rewrite pru17; clear - SL0; zlia).
assert (ALQ : bv_unsigned (w64 QSv) mod page_size = 0) by (rewrite UQS; unfold page_size; exact QA).
pose proof (commit_AI tfibsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(clear; zlia) CEILT PLACE SL1) as [CG BUD].
pose proof (commit_eager tfibsegs (w_H Wy) (w_A Wy) mdN false (Z_to_bv 64 50) (w64 QSv) 131072 HAI MWF0 nores50 ALQ ltac:(clear; zlia) CEILT PLACE SL1) as EG.
pose proof (commit_nonempty false (Z_to_bv 64 50) (w64 QSv) (Z_to_bv 64 (page_round_up_Z 131072)) mdN ltac:(rewrite pru17; unfold w64 in Un; rewrite Un; clear; zlia) (proj2 MW)) as NZg.
rewrite pru17 in CG, BUD, EG, NZg. fold (w64 131072) in CG, BUD, EG, NZg.
pose proof (destroyed_AI tfibsegs (w_H Wy) (w_A Wy) mdN (w64 QSv) 131072 HAI MWF0 ALQ ltac:(clear; zlia) CEILT) as [CD _].
rewrite pru17 in CD. fold (w64 131072) in CD.
destruct (commit_node3 tfibsegs false regs (Z_to_bv 64 0x65a08) mem (seg_rom tfibsegs) mdN (Z_to_bv 64 50) (w64 QSv) 131072
(AI_halted _ _ _ _ HAI) R17 R10 ALQ ltac:(rewrite UQS; clear - F9; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *; zlia)
R11 ltac:(clear; zlia) CEILT R12 R13 core50 R14 R15 PLACE BUD) as (I & nx & bit & i0 & NODE & Bi0 & OUT).
rewrite pru17 in OUT. fold (w64 131072) in OUT.
assert (IOtr : forall m2, YG0b.same_io mdN m2 -> same_io md0 m2).
{ intros m2 (X1 & X2 & X3 & X4). destruct IO0 as (Y1 & Y2 & Y3 & Y4). unfold same_io. rewrite X1, X2, X3, X4. repeat split; assumption. }
exists I, nx, (fun _ => 1), (fun _ => false), i0.
split. { rewrite Ec, Hms, Hpc. exact NODE. }
split. { intros i _. destruct (OUT i) as (md_i & _ & _ & _ & -> & ->); cbn [cfg_model]; exact (proj1 CG). }
split. { intros i. apply Haok. right; reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros i _; reflexivity|].
assert (APQ0 : forall r y, In r (ss_mem S_V) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= y < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
split; [| exact (skel_u64 E' false r y HE CK1 Hy)]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
split; [intros i E; discriminate E|].
intros i _.
destruct (OUT i) as (md_i & Hh_i & IO_i & Bv & NX & MD).
rewrite NX. rewrite MD in IO_i |- *.
set (md5 := grant_md false (Z_to_bv 64 50) (w64 QSv) (w64 131072) mdN) in *.
pose proof (grant_piece_shape (w64 QSv) (w64 131072) mdN) as (SH1 & SH2' & SH3 & SH4). cbv zeta in SH1, SH2', SH3, SH4. fold md5 in SH1, SH2', SH3, SH4.
assert (AL1 : QSv <= QSv + 131072) by (clear; zlia).
assert (AL2 : QSv mod page_size = 0) by (unfold page_size; exact QA).
assert (AL3 : (QSv + 131072) mod page_size = 0).
{ unfold page_size. clear - QA. apply Z.mod_divide in QA as [q' Hq]; [|zlia]. rewrite Hq. apply Z.mod_divide; [zlia|]. exists (q' + 32). zlia. }
destruct (allow_expose tfibsegs Wy md5 QSv (QSv + 131072) AL1 AL2 AL3 (proj1 CG) ltac:(rewrite SH3; clear - EG SL0; zlia)) as (LE5 & A5 & AB5 & VIS5 & MON5 & AI5).
set (W5 := wallow tfibsegs Wy QSv (QSv + 131072) AL1 AL2 AL3) in *.
assert (SUB : hsub (w_H W5) (w_H Wy)).
{ intros x Hx. destruct (w_H Wy x) eqn:Ex; [reflexivity|]. rewrite (MON5 x Ex) in Hx. discriminate Hx. }
eapply (amreal_world_le tfibsegs _ Wy W5); [exact LE5 | intros _; exact AI5 |].
apply (GRANT W5); [exact LE5 | exact SUB | exact MON5 | exact A5 | exact VIS5
| intros x Nx; unfold W5, wallow; cbn [w_H]; apply Hcut_out; exact Nx
| exact AI5 | split; [apply (proj2 (amwf_MWF md5)); exact (proj2 CG) | exact NZg] | exact (IOtr _ IO_i) | exact EG
| rewrite SH1, SH2', SH3, SH4; repeat split; reflexivity |].
assert (FRz : forall x : word, ~ QR (bv_unsigned x) -> zfill (w64 QSv) (w64 131072) mem x = mem x).
{ intros x Hx. apply zfill_out. rewrite UQS, Un. pose proof (EQR (bv_unsigned x)) as EQx. clear - Hx EQx.
destruct (Z_lt_le_dec (bv_unsigned x) QSv); [left; zlia|]. right. destruct (Z_lt_le_dec (bv_unsigned x) (QSv + 131072)); [exfalso; apply Hx; apply EQx; zlia | zlia]. }
assert (APQ : forall r y, In r (ss_mem S_V) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= y < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ QR y /\ 0 <= y < 2 ^ 64).
{ intros r y Hr Hy.
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) (ss_mem S_V) = true) r Hr) as CK.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
split; [| exact (skel_u64 E' false r y HE CK1 Hy)]. intros Hq. apply (proj1 (EQR y)) in Hq.
pose proof (skel_apart_Q E' r HE CK1 NB) as AP. clear - Hy Hq AP Q5 F9. zlia. }
pose proof (at_N_cont Wy W5 md5 WIN (PSR W5 SH2 (fun m => R m /\ ZQF W5 m)) S_V TQ (w64 QSv) QR (zfill (w64 QSv) (w64 131072) mem) ms E'
HE HS Hrv MEQ PRS SUB ltac:(rewrite <- R10, (Hregs 10%bv), H10; reflexivity) Hnc ltac:(intros x Hx; rewrite Hms; cbn [ms_mem pend_at]; exact (FRz x Hx))
APQ
(fun r y Hr Hy => APQ r y Hr ltac:(pose proof (region_wf_facts r (regions_wf_In _ r (proj1 Hmem) Hr)) as (_ & WW & _); clear - Hy WW; zlia))
ltac:(intros y Hy Hq; apply (proj1 (EQR y)) in Hq; destruct Hsp as (S1 & _ & S3 & _); pose proof (lo_stk_ceil ly LY) as SC;
clear - Hy Hq S1 S3 SC Q5 F10; ceil; unfold ASAN_CEIL, AFSTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia)) as C.
rewrite Hms in C. cbn [ms_regs ms_mem pend_at] in C. rewrite Hpc, Hres_g in C. apply C. clear C.
rewrite Hms in HPm. cbn [ms_mem pend_at] in HPm. destruct HPm as [(HB & HM & HSH & HRs) HR0].
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (NQR : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ QR a /\ bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. split.
- intros Hq. apply (proj1 (EQR a)) in Hq. clear - Ha Hq MQ Q5 F9 F10 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
- apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in *. zlia. }
split; [split; [|split; [|split]]|split].
-   intros j Hj. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof (lo_stk_ceil ly LY) as SC. destruct Hbp as (BP1 & BP2 & _).
intros kk Hkk. pose proof (HB j Hj kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 <= A < ly_stk_hi ly) by (clear - Hj Hkk LEN BP1 BP2; zlia);
assert (UA : bv_unsigned (Z_to_bv 64 A) = A) by
(apply unsigned_lit_small; clear - RNG S1 S3 T4 T7 U2 SC; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AFSTACK, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; try unfold sp0 in *; zlia);
assert (NQ : ~ QR A) by
(intros Hq; apply (proj1 (EQR _)) in Hq; clear - RNG Hq S1 SC Q5 F10 MZ; ceil; unfold ASAN_CEIL, AFSTACK, kPtrArrayResv in *; try unfold sp0 in *; try unfold Qb in *; zlia);
assert (HW5 : w_H W5 (Z_to_bv 64 A) = w_H Wy (Z_to_bv 64 A)) by
(unfold W5, wallow; cbn [w_H]; apply Hcut_out; rewrite UA; intros HQ; apply NQ; apply (proj2 (EQR A)); exact HQ);
unfold mbyte, mrestrict in X |- *; rewrite HW5; rewrite (FRz (Z_to_bv 64 A)); [exact X | rewrite UA; exact NQ]
end.
- intros a Ha. destruct (NQR a (or_introl Ha)) as [Nq Ua]. destruct (HM a Ha) as [Hh [b Hb]]. split; [exact (MON5 _ Hh)|]. exists b. rewrite FRz; [exact Hb | rewrite Ua; exact Nq].
- intros a Ha. destruct (NQR a (or_intror Ha)) as [Nq Ua]. destruct (HSH a Ha) as [Hh [b Hb]]. split; [exact (MON5 _ Hh)|]. exists b. rewrite FRz; [exact Hb | rewrite Ua; exact Nq].
- pose proof SH_ok as (_ & _ & OK2). apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (unfold run_ok in RO; clear - RO Ha MZ; zlia).
destruct (NQR a PL) as [Nq Ua]. unfold w64. rewrite FRz by (rewrite Ua; exact Nq). exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- exact (RQ mem _ FRz HR0).
- intros a Hq. pose proof (proj1 (EQR a) Hq) as Ra.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia).
split; [apply VIS5; rewrite Ua; exact Ra|]. apply zfill_in. rewrite UQS, Un, Ua. exact Ra.
Qed.
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition RZF (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQF Wy m.
Definition RZ (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop := R m /\ ZQ Wy m.
Lemma ZQF_rstable : idx = res -> rstable (ZQF Wy).
Proof.
intros Heq. pose proof (QR_facts Heq) as (E1 & _ & _ & F9 & Q5 & F10 & EQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. destruct Hmap_apart as (_ & _ & _ & MQ & _). unfold zdisjoint in MQ. cbn [fst snd] in MQ.
assert (U64 : forall a, QR a -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. pose proof (proj1 (EQ a) Ha) as Ra. apply unsigned_lit_small. clear - Ra F9 F10 Q5 E1 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in *; try unfold Qb in *; zlia. }
split.
- intros m m' FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. intros Hw. destruct Hw as [Hw|Hw].
+ destruct (Z_lt_le_dec a (QSv + 8)) as [Hl|Hg].
* exact (QS_not_WIN1R a ltac:(clear - Ra Hl MZ; zlia) (or_introl Hw)).
* exact (QR_not_WIN1T Heq a Ha ltac:(clear - Hg MZ; zlia) (or_introl Hw)).
+ pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - Hw Ra MQ Q5 F9 Z8 MZ. unfold kPtrArrayResv, SEC_NMAX in *. try unfold Qb in *. zlia.
- intros m m' d len Hp FR H a Ha. destruct (H a Ha) as [H1 H2]. split; [exact H1|]. rewrite FR; [exact H2|]. rewrite (U64 a Ha).
pose proof (proj1 (EQ a) Ha) as Ra. clear - Hp Ra MQ F9 F10 Q5 M1 M2 SM1 SM2 E1 Heq MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold Qb in *. zlia.
Qed.
Local Ltac s_runR HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runR Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma segV : forall (R : (word -> option byte) -> Prop), rstable R -> idx = res ->
forall c, at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZF R)) S_VG Wy c ->
SRr tfibsegs Wy c (at_S Wy md1 (fun a => WIN a \/ QR a) (PSR Wy SH2 (RZ R)) S_YJ).
Proof.
intros R RS Heq c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (rstable_and _ _ RS (ZQF_rstable Heq)) as RS2.
pose proof (PSR_stable Wy SH2 (RZF R) OK2 RS2) as HP2.
assert (HX : forall a, WIN1R a -> WIN a \/ QR a) by (intros a Ha; left; exact (WIN1R_WIN a Ha)).
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv in F9, F10. unfold kMaxNumChunks in HI, HRS.
pose proof (QR_facts Heq) as (E1 & _ & _ & _ & Q5 & _ & EQR).
s_runR HR tfibtbl_rtC tfibtbl_rtC_ok 0x369ac S_V2 HX HP2.
s_runR HR tfibtbl_rtA tfibtbl_rtA_ok 0x367c8 S_V3 HX HP2.
s_pin HR (12%bv : bv 5) (SOff aQS 0).
{ clear - HI F9 F10. pin_zevS. rewrite EaQS, EaQ, EaNCH. unfold w64. unfold QSv in *. rewrite !unsigned_lit_small by (try unfold Qb in *; zlia).
zcanon_simp. land_lits. rewrite Z.shiftl_mul_pow2 by zlia. change (2 ^ 3) with 8. zcanon_simp. try unfold Qb in *. zlia. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs1 := eval vm_compute in (setchunks (Some aINST) o_sec_reserved [YP09.mkChunk o_sec_reserved (CVal 8 RES2T)] (ss_mem ss)) in
apply (at_S_setchunks Wy md1 X0 _ ss _ _ (Some aINST) o_sec_reserved [YP09.mkChunk o_sec_reserved (CVal 8 RES2T)]) in HR;
[ change (setchunks _ _ _ (ss_mem ss)) with rs1 in HR; cbn [ss_pc ss_regs ss_resv ss_facts] in HR | vm_compute; reflexivity | ] end.
2:{ intros E' m HE _ r Hr Hb Hl RO.
lazymatch type of Hr with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => negb (YP09.obase_eqb (YP09.r_base r) (Some aINST) && Z.eqb (YP09.r_lo r) o_sec_reserved)
|| existsb (fun c => chunk_eqb c (YP09.mkChunk o_sec_reserved (CVal 8 (SOff aRES 16384)))) (YP09.r_chunks r)) l = true) r Hr) as CK end.
cbn beta in CK. rewrite Hb, Hl in CK. cbn [YP09.obase_eqb] in CK. rewrite Nat.eqb_refl, Z.eqb_refl in CK. cbn [andb negb orb] in CK.
destruct RO as (_ & _ & _ & RC). apply Forall_cons; [|apply Forall_nil].
apply existsb_exists in CK as (k0 & Hk0 & CK). apply chunk_eqb_eq in CK. subst k0.
pose proof (proj1 (Forall_forall _ _) RC _ Hk0) as RC0. rewrite Hb in RC0. apply (chunk_ok_CVal_eqv E' _ _ _ _ RES2T (SOff aRES 16384)); [|exact RC0].
apply (sv_denot_eq_of_U E' _ _ HE); [vm_compute; reflexivity | vm_compute; reflexivity | exact (RES2T_eq Heq)]. }
lazymatch type of HR with at_S _ _ ?X0 _ ?ss _ _ =>
let rs := eval vm_compute in (trimscratch (-272) (ss_mem ss)) in
apply (at_S_submem Wy md1 X0 _ ss _ _ rs) in HR; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X P ss W' c' sJY [1; 15; 17; 20]%bv HR ltac:(unfold sHAV, sJY; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR.
lazymatch type of HR with at_S _ _ ?X0 _ _ _ _ =>
apply (at_S_addreg Wy md1 X0 _ _ _ _ R_qs) in HR; [| reflexivity |] end.
2:{ intros E' m HE MEQ PRS [HP [HQ HZ]] HM. pose proof (proj1 HE) as HEn.
assert (BQ : base_val E' (Some aQS) = QSv).
{ cbn [base_val]. unfold aQS. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64. apply unsigned_lit_small. clear - HI F9 F10. unfold QSv in *. try unfold Qb in *. zlia. }
split.
- unfold region_ok, R_qs. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BQ.
split; [clear - HI F9; unfold QSv in *; try unfold Qb in *; zlia|]. split; [clear - HI F9 F10; unfold QSv in *; try unfold Qb in *; zlia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable_off; [off_by ltac:(clear - Ho HI F9 F10; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSv, TFIB_IMG_END in *; try unfold Qb in *; zlia) |].
destruct (HZ (QSv + o) ltac:(apply (proj2 (EQR _)); clear - Ho; zlia)) as [Hh Hz]. split; [exact Hh | exists (Z_to_bv 8 0); exact Hz].
- intros r2 Hr2. unfold extent_disjoint, R_qs. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BQ.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r) && negb (obase_eqb (YP09.r_base r) (Some aQS))) l = true) r2 Hr2) as CK end.
cbn beta in CK. apply andb_prop in CK as [CK1 CK2].
assert (NB : YP09.r_base r2 <> Some aQS) by (intros Eq; rewrite Eq in CK2; discriminate CK2).
pose proof (skel_apart_QS E' false r2 HE CK1 NB) as AP. clear - AP. zlia. }
replace (addreg R_qs _) with S_YJ in HR by (rewrite <- S_VY_join; vm_compute; reflexivity).
apply SRr_ret. eapply at_S_weaken; [exact HR | intros a Ha; exact Ha | intros m [HP [HQ HZ]]; exact (conj HP (conj HQ (ZQ_of_ZQF Wy m HZ)))].
Qed.
End g.
End f.
