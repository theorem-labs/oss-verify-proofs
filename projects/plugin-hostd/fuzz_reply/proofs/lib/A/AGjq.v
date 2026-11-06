(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjq.v (a working branch 30a1993588f, c5 + memnorm; file sha256 a7886c3941d1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 60 image addresses moved by code-verified function pairs (58 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 3 hand maps (agreloc-resolve-R.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AE3d AB1q AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm AGid AGie AGif AGig AGjh AGjn AGjo AGjk AGjl AGjp.
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
(* can_fill, x15 at Allocate's entry (AGhy.REGS_G): atom 15, in {0, 1} by AGhy.frame_facts. *)
Let cfv : Z := bv_unsigned (getr regs0 15).
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
Local Abbreviation E11 := (@AGjm.E11 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E12 := (@AGjm.E12 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E13 := (@AGjm.E13 ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
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
Local Abbreviation runs_not_hi := (@AGjo.runs_not_hi _ ly regs0 n tr idx res mb LY Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart).
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
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Local Abbreviation QR := (@AGjp.QR ly res).
Hypothesis D1w : forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 BPv -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x31f84 ->
bv_unsigned (getr regs 2) = sp0 - 128 ->
PBUFW Wy mem -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (INSTv + o_sec_mutex + k) = Some 0) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x31f84) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 128 - DEP_STK <= bv_unsigned x < sp0 - 128) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Local Abbreviation segT1 := (@AGjp.segT1 _ _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart Wy md1 RX RXt).
Local Abbreviation DX := (@AGjp.DX ly regs0).
Hypothesis RXd : pstable DX RX.
Local Abbreviation PD := (@AGjp.PD ly mem0 DPOST Wy).
Local Abbreviation PD_rstable := (@AGjp.PD_rstable _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy).
Local Abbreviation PD_stableT := (@AGjp.PD_stableT _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy).
Local Abbreviation PSR_stableS := (@AGjp.PSR_stableS _ ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart Wy).
Local Abbreviation PD_stableS := (@AGjp.PD_stableS _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy).
Local Abbreviation PDX := (@AGjp.PDX ly mem0 DPOST Wy RX).
Local Abbreviation PDX_rstable := (@AGjp.PDX_rstable _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy RX RXs).
Local Abbreviation PDX_stableT := (@AGjp.PDX_stableT _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy RX RXt).
Local Abbreviation PDX_stableS := (@AGjp.PDX_stableS _ ly regs0 mem0 n tr idx res mb LY IMG Hsp Htrlen Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST Wy RX RXt).
Local Abbreviation dx_okb := (@AGjp.dx_okb).
Local Abbreviation skel_apart_DX := (@AGjp.skel_apart_DX _ ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@AGjp.skel_apart_stk _ ly regs0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@AGjp.at_S_depot _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def Wy md1 RX D1w RXd).
Local Abbreviation SH3 := (@AGjp.SH3 n mb).
Local Abbreviation SH4 := (@AGjp.SH4 n mb).
Local Abbreviation shadow_marks := (@AGjp.shadow_marks _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@AGjp.SH34_ok _ ly regs0 n tr idx res mb Htrlen Hinst Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@AGjp.segT2b _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def Wy md1 RX RXs RXt).
Local Abbreviation segT2 := (@AGjp.segT2 _ _ W ly regs0 mem0 n tr idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Htrlen Hso Hbp Hinst Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def Wy md1 RX RXs RXt).
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Local Ltac s_runT HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runT Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition SH5 : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768 + N8D / 8, SHBv + UEv / 8, 0)].
Definition SH6 : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5.
Lemma user_marks : 8064 <= N8D / 8 <= R8v / 8 /\ (n mod 8 = 0 -> N8D / 8 = R8v / 8) /\ (n mod 8 <> 0 -> N8D / 8 + 1 = R8v / 8) /\ PBv = SMv + 768 + N8D / 8 /\ Uv = mb + 6144.
Proof.
pose proof map_facts as (_ & _ & _ & _ & U5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & PB & _). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, NR. clear - U5 PB Z1 Z2 Z3 Z4 Z5 Z6 NR MZ.
apply Z.mod_divide in Z2 as [q Hq]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hq, Hp in *. rewrite !Z_div_mult by zlia.
unfold R8v, N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as B1.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)) as B2.
repeat split; try zlia; intros H8; nia.
Qed.
Lemma SH56_ok : Forall run_ok SH5 /\ Forall run_ok SH6.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B5 Z8.
unfold SH5, SH6, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section U.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
Hypothesis Hsmall : N8D / 8 < 18446744073709551615.
Let place_X : forall d len a, ((mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)) -> d <= a < d + len -> X a :=
fun d len a PL Ha => HXW a (place_WIN d len a PL Ha).
Local Ltac s_memsetR HR ss' k d len vb retpc OK RS :=
lazymatch type of HR with at_S ?Wx ?md ?X (PSR _ ?sh ?R) ?ss ?W' ?c' =>
let ed := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in
let el := eval vm_compute in (sr_get (ss_regs ss) 12%bv) in
let Ud := fresh "Ud" in let Ul := fresh "Ul" in let PL := fresh "PL" in
assert (Ud : U E0 ed = d); [|
assert (Ul : U E0 el = len); [|
assert (PL : (mb + 6144 <= d /\ d + len <= mb + MSv) \/ (SMv <= d /\ d + len <= SMv + MSv / 8)); [|
eapply SRr_bind;
[ eapply (at_S_memsetSR Wx md X sh R ss W' c' k ed el d len vb retpc HR RS eq_refl ltac:(vm_compute; reflexivity) ltac:(unfold sHAV; cbv; zlia)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Ud Ul);
[ (clear; zlia) || zlia | clear; cbv; reflexivity | clear; zlia | clear; zlia | exact PL | exact OK | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (place_X d len a PL Ha)
| exact (memset_ext_of_skel false d len ss ltac:(vm_compute; reflexivity) PL ltac:(intros XX; discriminate XX))
| exact (memset_u64_of_skel false ss ltac:(vm_compute; reflexivity)) ]
| clear HR Ud Ul; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR;
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with ss' in HR by (vm_compute; reflexivity) end ] ] ] ] end.
Lemma segU1 : forall W' c, at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ).
Proof.
intros W1 c HR. pose proof SH34_ok as [_ OK4]. pose proof SH56_ok as [OK5 _]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH4 (PDX z) OK4 (PDX_stableS z)) as HP4. pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_LTU true USH_LEN (SLit 18446744073709551615).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR Hsmall MZ. arm_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. apply Z.ltb_lt. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x96900 U_M5 HX HP4.
s_memsetR HR U_Q sM5 constr:(SMv + 768) constr:(N8D / 8) 0 0x32090 OK4 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, AGjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 Z4 Z5 NR MZ. U_zevS. unfold USH_LEN. cbn [zev zalu_raw]. unfold_atoms. rewrite EaMAP, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6136 + (p * 8 + 0)) with ((u * 512 + 767 + p) * 8) by zlia. replace (u * 4096 + 6144) with ((u * 512 + 768) * 8) by zlia.
rewrite !Z_div_mult in * by zlia. zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 B1 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH5 (PDX z) U_Q) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH4 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + UEv / 8 <? SMv + 768) = false) by (clear - A2 A5 MZ; apply Z.ltb_ge; zlia).
assert (G2 : (SMv + 768 + N8D / 8 <? SMv + MSv / 8) = true) by (clear - A2 A3 A5 A6 B1 MZ; apply Z.ltb_lt; zlia).
assert (G3 : (SMv + 512 <? SMv + 768) = true) by (apply Z.ltb_lt; zlia).
assert (G4 : (SMv + 768 + N8D / 8 <? SMv + 768) = false) by (clear - B1 MZ; apply Z.ltb_ge; zlia).
assert (G5 : (SMv <? SMv + 768) = true) by (apply Z.ltb_lt; zlia).
assert (G6 : (SMv + 768 + N8D / 8 <? SMv + 512) = false) by (clear - B1 MZ; apply Z.ltb_ge; zlia).
assert (G7 : (SMv + 768 <? SMv + 768) = false) by (apply Z.ltb_irrefl).
rewrite G1, G2, G3, G4, G5, G6, G7 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3.
pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail B2'))) as C4'. clear B2'.
rewrite Z.max_l in C1 by (clear - A2 A5 B1 MZ; zlia). rewrite Z.min_l in C2 by zlia. rewrite Z.min_l in C3 by zlia.
unfold SH5. apply Forall_cons; [exact C0|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [exact C3|].
apply Forall_cons; [|apply Forall_nil].
destruct (SMv + 768 + N8D / 8 <? SHBv + UEv / 8) eqn:G8; cbn [app] in C4'.
- pose proof (Forall_inv C4') as C4. rewrite Z.max_r in C4 by (clear - B1 MZ; zlia). exact C4.
- apply Z.ltb_ge in G8. intros a Ha. cbn [fst snd] in Ha. exfalso. clear - G8 Ha MZ. zlia. }
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
apply (at_S_submem Wx md X0 P ss W' c' (trimscratch (-128) (ss_mem U_Q))) in HR; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
s_forget HR kJQ CLOBJ. s_noconds HR. s_station HR U_QJ.
apply SRr_ret. exact HR.
Qed.
Lemma SH6_of_cut : forall m, Forall (brun m) ((Uv, Uv + 4096, 190) :: cut Uv (Uv + 4096) SH5) -> Forall (brun m) SH6.
Proof.
intros m HF. pose proof (Forall_inv HF) as C0. pose proof (Forall_inv_tail HF) as B'. clear HF.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & _ & _ & B5).
pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold cut, SH5 in B'. cbn [flat_map app] in B'. unfold cut1 in B'. cbn [fst snd] in B'.
destruct MZ as [ZLO|ZHI].
-
assert (BOT : Uv + 4096 < SMv) by (clear - ZLO B5 Z8; unfold SEC_NMAX in *; zlia).
assert (G1 : forall x, SMv <= x -> (x <? Uv) = false) by (intros x Hx; apply Z.ltb_ge; clear - Hx BOT; zlia).
assert (G2 : forall x, SMv <= x -> (Uv + 4096 <? x) = true) by (intros x Hx; apply Z.ltb_lt; clear - Hx BOT; zlia).
rewrite !G1 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). rewrite !G2 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). cbn [app] in B'.
rewrite !Z.max_l in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 BOT; zlia).
unfold SH6, SH5. apply Forall_cons; [exact C0 | exact B'].
-
assert (TOP : SMv + MSv / 8 < Uv) by (clear - ZHI B5; zlia).
assert (G1 : forall x, x <= SMv + MSv / 8 -> (x <? Uv) = true) by (intros x Hx; apply Z.ltb_lt; clear - Hx TOP; zlia).
assert (G2 : forall x, x <= SMv + MSv / 8 -> (Uv + 4096 <? x) = false) by (intros x Hx; apply Z.ltb_ge; clear - Hx TOP; zlia).
rewrite !G1 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). rewrite !G2 in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1; zlia). cbn [app] in B'.
rewrite !Z.min_l in B' by (clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 TOP; zlia).
unfold SH6, SH5. apply Forall_cons; [exact C0 | exact B'].
Qed.
Lemma segUe : cfv <> 0 -> n mod 8 = 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH6 (PDX z)) Ue_RET).
Proof.
intros Hcf H8 W1 c HR. pose proof SH56_ok as [OK5 OK6]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5. pose proof (PSR_stableS SH6 (PDX z) OK6 (PDX_stableS z)) as HP6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_EQ true (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_eq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)). zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32280 (runto 0x32280 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ)) HX HP5.
s_arm HR BC_EQ false (SOff 15 0) (SLit 0).
{ clear - Hcf. arm_zevS. rewrite (Er 15 15%bv eq_refl). pose proof (u64_range (getr regs0 15)) as U15. zcanon_simp. apply Z.eqb_neq. unfold cfv in Hcf. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x96900 Ue_MF HX HP5.
s_memsetR HR (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x322b8) sMF constr:(Uv) 4096 190 0x322b8 OK5 RS.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. reflexivity. }
{ left. clear - Z8 B5 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH6 (PDX z)) in HR; [|exact SH6_of_cut].
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e0 (runto 0x322e0 (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x322b8)) HX HP6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e8 (runto 0x322e8 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x322e0 (ss_after_stretch Ue_MF (ss_mem Ue_MF) sMF CLOB_MS 0x322b8)))) HX HP6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32348 Ue_RET HX HP6.
apply SRr_ret. exact HR.
Qed.
Lemma segUe0 : cfv = 0 -> n mod 8 = 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH5 (PDX z)) Ue_RET0).
Proof.
intros Hcf H8 W1 c HR. pose proof SH56_ok as [OK5 OK6]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5. pose proof (PSR_stableS SH6 (PDX z) OK6 (PDX_stableS z)) as HP6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5).
s_arm HR BC_EQ true (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_eq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)). zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32280 (runto 0x32280 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ)) HX HP5.
s_arm HR BC_EQ true (SOff 15 0) (SLit 0).
{ clear - Hcf. arm_zevS. rewrite (Er 15 15%bv eq_refl). pose proof (u64_range (getr regs0 15)) as U15. zcanon_simp. apply Z.eqb_eq. unfold cfv in Hcf. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e0 (runto 0x322e0 (stV0 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ))) HX HP5.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e8 (runto 0x322e8 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x322e0 (stV0 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ))))) HX HP5.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32348 Ue_RET0 HX HP5.
apply SRr_ret. exact HR.
Qed.
Definition PT (sh : list (Z * Z * Z)) (R : (word -> option byte) -> Prop) (m : word -> option byte) : Prop :=
PBUFW Wy m /\ (forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wy) m a) /\
(forall a, SMv <= a < SMv + MSv / 8 -> a <> PBv -> apresent (w_H Wy) m a) /\ Forall (brun m) sh /\ R m.
Definition run_okT (r : Z * Z * Z) : Prop := run_ok r /\ (snd (fst r) <= PBv \/ PBv + 1 <= fst (fst r)).
Definition SH5o : list (Z * Z * Z) :=
[(SMv + 768, SMv + 768 + N8D / 8, 0); (SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (PBv + 1, SHBv + UEv / 8, 0)].
Definition SH6o : list (Z * Z * Z) := (Uv, Uv + 4096, 190) :: SH5o.
Lemma SH56o_ok : n mod 8 <> 0 -> Forall run_okT SH5o /\ Forall run_okT SH6o.
Proof.
intros H8. pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). pose proof user_marks as (B1 & _ & B3 & B4 & B5). specialize (B3 H8).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. unfold kHighShadowEnd in SM2. clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 B1 B3 B4 B5 Z8 M1 SM2 MZ.
unfold SH5o, SH6o, run_okT, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Lemma PT_stableT : forall sh R, Forall run_okT sh -> pstable WIN1T R -> pstable WIN1T (PT sh R).
Proof.
intros sh R OK RS m m' FR (HB & HM & HSH & HR' & HQ).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> a <> PBv -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hne. apply FR. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 SM1 SM2 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *; zlia).
intros [Hw|[Hw|[Hw|Hw]]]; [exact (runs_not_WIN1S a Ha (or_introl Hw)) | exact (runs_not_WIN1S a Ha (or_intror (or_introl Hw))) | exact (runs_not_WIN1S a Ha (or_intror (or_intror Hw))) | clear - Hw Hne MZ; zlia]. }
split; [exact (PBUFW_stableT Wy m m' FR HB)|].
pose proof user_marks as (B1 & _ & _ & B4 & _). pose proof shadow_marks as (_ & A2 & A3 & _ & _ & A6 & _).
split; [intros a Ha; apply (apresent_same (w_H Wy) m); [apply (U a (or_introl Ha)); clear - Ha B4 B1 A2 A3 A6 M1 SM2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *; zlia | exact (HM a Ha)]|].
split; [intros a Ha Hne; apply (apresent_same (w_H Wy) m); [exact (U a (or_intror Ha) Hne) | exact (HSH a Ha Hne)]|].
split; [|exact (RS m m' FR HQ)].
apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK r Hr) as [RO RP]. pose proof (proj1 (Forall_forall _ _) HR' r Hr a Ha) as V.
rewrite (U a); [exact V | unfold run_ok in RO; clear - RO Ha MZ; zlia | clear - RP Ha MZ; zlia].
Qed.
Lemma segUoP : n mod 8 <> 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT SH5o (PDX z)) Uo_P).
Proof.
intros H8 W1 c HR. pose proof SH56_ok as [OK5 _]. pose proof (SH56o_ok H8) as [OK5o OK6o].
pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5.
pose proof (PT_stableT SH5o (PDX z) OK5o (PDX_stableT z)) as HT5. pose proof (PT_stableT SH6o (PDX z) OK6o (PDX_stableT z)) as HT6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
assert (HXT : forall a, WIN1T a -> X a) by (intros a Ha; apply HXW, WIN1T_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold kHighShadowBeg, kHighShadowEnd in SM1, SM2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5). specialize (B3 H8). pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (PLfill : (mb + 6144 <= Uv /\ Uv + 4096 <= mb + MSv) \/ (SMv <= Uv /\ Uv + 4096 <= SMv + MSv / 8)) by (left; clear - B5 Z8 MZ; zlia).
s_arm HR BC_EQ false (SOff 10 0) (SOff aN8DS 0).
{ clear - H8 NR Hn Z4 Z6 MZ. arm_zevS. rewrite E10, Hn, EaN8D. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq.
unfold N8D in *. pose proof (Z.div_mod n 8 ltac:(zlia)). zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x320bc Uo_L6 HX HP5.
s_ladderM s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32120 Uo_L6lo Uo_L6h Uo_L6h2 Uo_L6hi Uo_P0 sL6 CLOB_L6 HX HP5.
s_pin HR (10%bv : bv 5) (SOff aPBS 0).
{ clear - M1 M2 M3 Z8 Z4 Z5 NR A7 B4 MZ. pin_zevS. rewrite EaPB, (eq_refl : ew E0 47 = w64 SHBv), EaMAP, EaN8D. unfold w64, AGjm.SHBv in *.
rewrite B4 in *. rewrite A7 in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z5 as [p Hp]; [|zlia]. rewrite Hu, Hp in *.
replace (u * 4096 + 6144 + (p * 8 + 0)) with ((u * 512 + 768 + p) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
apply (at_S_addreg Wy md1 X _ _ _ _ R_pbS) in HR; [| reflexivity |].
2:{ intros E' m HE MEQ PRS [(HB & HM & HSH & HRs) HQ] HMok. pose proof (proj1 HE) as HEn.
assert (BP : base_val E' (Some aPBS) = PBv).
{ cbn [base_val]. unfold aPBS. rewrite (HEn 66%nat ltac:(unfold sHAV; zlia)), EaPB. unfold w64. apply unsigned_lit_small. clear - B4 B1 A2 A5 A3 A6 SM1 SM2 MZ. zlia. }
split.
- unfold region_ok, R_pbS. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BP.
split; [clear - B4 B1 SM1 MZ; zlia|]. split; [clear - B4 B1 A2 A3 A5 A6 SM2 MZ; zlia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable_off; [off_by ltac:(clear - Ho B4 B1 SM1 A2 A3 A5 A6 SM2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. apply HSH. clear - Ho B4 B1 A2 A3 A5 A6 MZ. zlia.
- intros r2 Hr2. unfold extent_disjoint, R_pbS. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BP.
lazymatch type of Hr2 with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => skel_okb false (skel r)) l = true) r2 Hr2) as CK end.
cbn beta in CK.
pose proof (skel_apart E' false PBv 1 HE ltac:(right; clear - B4 B1 A2 A3 A5 A6 MZ; zlia) ltac:(intros XX; discriminate XX) r2 CK) as AP. clear - AP. zlia. }
s_station HR Uo_P.
apply (at_S_weaken Wy md1 X X _ (PT SH5o (PDX z)) Uo_P) in HR; [| intros a Ha; exact Ha |].
2:{ intros m [(HB & HM & HSH & HRs) HQ]. split; [exact HB|]. split; [exact HM|]. split; [intros a Ha _; exact (HSH a Ha)|]. split; [|exact HQ].
unfold SH5o. unfold SH5 in HRs.
pose proof (Forall_inv HRs) as C1. pose proof (Forall_inv (Forall_inv_tail HRs)) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HRs))) as C3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs)))) as C4. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HRs))))) as C5.
repeat (apply Forall_cons); [exact C1 | exact C2 | exact C3 | exact C4 | | apply Forall_nil].
intros a Ha. apply C5. cbn [fst snd] in *. clear - Ha B4 MZ. zlia. }
apply SRr_ret. exact HR.
Qed.
Lemma segUo : cfv <> 0 -> n mod 8 <> 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT SH6o (PDX z)) Uo_RET).
Proof.
intros Hcf H8 W1 c HR. pose proof SH56_ok as [OK5 _]. pose proof (SH56o_ok H8) as [OK5o OK6o].
pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5.
pose proof (PT_stableT SH5o (PDX z) OK5o (PDX_stableT z)) as HT5. pose proof (PT_stableT SH6o (PDX z) OK6o (PDX_stableT z)) as HT6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
assert (HXT : forall a, WIN1T a -> X a) by (intros a Ha; apply HXW, WIN1T_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold kHighShadowBeg, kHighShadowEnd in SM1, SM2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5). specialize (B3 H8). pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (PLfill : (mb + 6144 <= Uv /\ Uv + 4096 <= mb + MSv) \/ (SMv <= Uv /\ Uv + 4096 <= SMv + MSv / 8)) by (left; clear - B5 Z8 MZ; zlia).
eapply SRr_bind; [ exact (segUoP H8 W1 c HR) | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ].
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x32280 (runto 0x32280 Uo_P) HXT HT5.
s_arm HR BC_EQ false (SOff 15 0) (SLit 0).
{ clear - Hcf. arm_zevS. rewrite (Er 15 15%bv eq_refl). pose proof (u64_range (getr regs0 15)) as U15. zcanon_simp. apply Z.eqb_neq. unfold cfv in Hcf. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x96900 Uo_MF HXT HT5.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
eapply SRr_bind;
[ eapply (at_S_memset Wx md X0 P (PT SH6o (PDX z)) ss W' c' sMF (SOff aMAP 6144) (SLit 4096) Uv 4096 190 0x322b8 HR eq_refl ltac:(vm_compute; reflexivity) ltac:(unfold sHAV, sMF; zlia)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
| clear HR; let W3 := fresh "Wm" in let c3 := fresh "cm" in intros W3 c3 _ HR ] end.
{ clear - M1 M2 Z8 B5 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
{ clear. U_zevS. reflexivity. }
{ clear; zlia. }
{ clear - M1 B5 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END. zlia. }
{ clear - M2 Z8 B5 MZ. zlia. }
{ clear; cbv; reflexivity. }
{ clear; zlia. }
{ clear; zlia. }
{ intros m MEQ (HB & HM & HSH & HRs & HQ) a Ha. apply HM. clear - Ha B5 Z8 MZ. zlia. }
{ refine (memset_ext_of_skel true Uv 4096 Uo_MF ltac:(vm_compute; reflexivity) PLfill _); intros _; clear - B1 B4 B5 M1 SM2 A2 A3 A5 A6 MZ; zlia. }
{ exact (memset_u64_of_skel true Uo_MF ltac:(vm_compute; reflexivity)). }
{ intros m m' MEQ (HB & HM & HSH & HRs & HQ) FR FILL.
assert (FR' : forall a, 0 <= a < 2 ^ 64 -> ~ (Uv <= a < Uv + 4096) -> m' (w64 a) = m (w64 a)).
{ intros a Ha Hna. apply FR. unfold w64. rewrite unsigned_lit_small by exact Ha. exact Hna. }
assert (TOP : SMv + MSv / 8 < Uv \/ Uv + 4096 < SMv) by (clear - B5 Z8 MZ; unfold SEC_NMAX in *; zlia).
split; [|split; [|split; [|split]]].
- intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. pose proof tr_length as LEN.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). pose proof Hsp as (S1 & _ & S3 & _). pose proof Hbp as (BP1 & BP2 & _).
apply FR'; [clear - Hi Hkk LEN T4 T7 S1 S3 BP1 BP2 MZ; unfold AFSTACK, kHighMemBeg, kHighMemEnd in *; zlia|]. intros Hin.
apply (runs_not_hi (BPv + 8 * Z.of_nat i + Z.of_nat kk)); [left; clear - Hin B5 Z8 MZ; zlia | clear - Hi Hkk LEN BP1 BP2 MZ; zlia].
- intros a Ha. destruct (HM a Ha) as [Hh [b Hb]]. split; [exact Hh|].
destruct (Z_lt_le_dec a (Uv + 4096)) as [L|GE].
+ exists (Z_to_bv 8 190). apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 Z8 MZ; zlia). clear - Ha L B5 MZ; zlia.
+ exists b. rewrite <- Hb. apply (FR' a); clear - Ha GE M1 M2 Z8 MZ; zlia.
- intros a Ha Hne. destruct (HSH a Ha Hne) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- Hb. apply (FR' a); [clear - Ha SM1 SM2 MZ; zlia | clear - Ha TOP MZ; zlia].
- unfold SH6o. apply Forall_cons.
+ intros a Ha. cbn [fst snd] in Ha. apply FILL. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 Z8 B5 MZ; zlia). exact Ha.
+ apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK5o r Hr) as [RO _].
rewrite FR'; [exact (proj1 (Forall_forall _ _) HRs r Hr a Ha) | unfold run_ok in RO; clear - RO Ha M1 M2 SM1 SM2 Z8 MZ; zlia |].
unfold run_ok in RO. unfold SH5o in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Ha; clear - Ha TOP B1 B4 A2 A3 A5 A6 MZ; zlia.
- destruct HQ as [(memD & D1' & D2 & D3) HRX]. split; [| exact (proj2 RXs m m' Uv 4096 PLfill FR HRX)].
exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hin. exact (proj1 (DZONE_disj _ Hx) (place_WIN Uv 4096 _ PLfill Hin)). }
apply (at_S_weaken Wy md1 _ X _ (PT SH6o (PDX z))) in HR; [| intros a [Ha|Ha]; [exact Ha | exact (HXW a (place_WIN Uv 4096 a PLfill Ha))] | intros m Hm; exact Hm].
lazymatch type of HR with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x322b8) in HR by (vm_compute; reflexivity) end.
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e0 (runto 0x322e0 (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x322b8)) HXT HT6.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e8 (runto 0x322e8 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x322e0 (ss_after_stretch Uo_MF (ss_mem Uo_MF) sMF CLOB_MS 0x322b8)))) HXT HT6.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x32348 Uo_RET HXT HT6.
apply SRr_ret. exact HR.
Qed.
Lemma segUo0 : cfv = 0 -> n mod 8 <> 0 -> forall W' c, at_S Wy md1 X (PSR Wy SH5 (PDX z)) U_QJ W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PT SH5o (PDX z)) Uo_RET0).
Proof.
intros Hcf H8 W1 c HR. pose proof SH56_ok as [OK5 _]. pose proof (SH56o_ok H8) as [OK5o OK6o].
pose proof (PSR_stableS SH5 (PDX z) OK5 (PDX_stableS z)) as HP5.
pose proof (PT_stableT SH5o (PDX z) OK5o (PDX_stableT z)) as HT5. pose proof (PT_stableT SH6o (PDX z) OK6o (PDX_stableT z)) as HT6.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
assert (HXT : forall a, WIN1T a -> X a) by (intros a Ha; apply HXW, WIN1T_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold kHighShadowBeg, kHighShadowEnd in SM1, SM2.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
pose proof user_marks as (B1 & B2 & B3 & B4 & B5). specialize (B3 H8). pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
assert (PLfill : (mb + 6144 <= Uv /\ Uv + 4096 <= mb + MSv) \/ (SMv <= Uv /\ Uv + 4096 <= SMv + MSv / 8)) by (left; clear - B5 Z8 MZ; zlia).
eapply SRr_bind; [ exact (segUoP H8 W1 c HR) | clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ].
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x32280 (runto 0x32280 Uo_P) HXT HT5.
s_arm HR BC_EQ true (SOff 15 0) (SLit 0).
{ clear - Hcf. arm_zevS. rewrite (Er 15 15%bv eq_refl). pose proof (u64_range (getr regs0 15)) as U15. zcanon_simp. apply Z.eqb_eq. unfold cfv in Hcf. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e0 (runto 0x322e0 (stV0 Uo_P)) HXT HT5.
s_arm HR BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.eqb_neq. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e8 (runto 0x322e8 (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x322e0 (stV0 Uo_P)))) HXT HT5.
s_arm HR BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112).
{ clear - M1 M2 Z8 MZ. arm_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. apply Z.ltb_ge. zlia. }
s_runT HR tfibtbl_rtA tfibtbl_rtA_ok 0x32348 Uo_RET0 HXT HT5.
apply SRr_ret. exact HR.
Qed.
End U.
End g.
End f.
