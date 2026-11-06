(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjp.v (a working branch 84ee52cd012, file sha256 d22ba5837835) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 42 image addresses moved by code-verified function pairs (67 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AB1q AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm AGid AGie AGif AGjh AGjn AGjo AGjk AGjl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
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
Hypothesis Hinst : 0x9f000 <= INSTv /\ INSTv + 0xe60 <= 0x12a1a0 /\ INSTv mod 8 = 0.
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
Local Abbreviation DZONE_disj_hi := (@AGjm.DZONE_disj_hi _ ly regs0 LY IMG Hsp).
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
Variables (Wy : world tfibsegs) (md1 : Model).
Variable RX : (word -> option byte) -> Prop.
Hypothesis RXs : rstable RX.
Hypothesis RXt : pstable WIN1T RX.
Definition QR (a : Z) : Prop := Qb + 8 * res <= a < Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit /\ a < Qb + kPtrArrayResv.
Hypothesis D1w : forall (X : Z -> Prop) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
(forall a, X a -> WIN a \/ QR a) ->
getr regs 10 = Z_to_bv 64 BPv -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = getr regs0 3 -> getr regs 4 = Z_to_bv 64 TFIB_TP -> getr regs 1 = Z_to_bv 64 0x322a0 ->
bv_unsigned (getr regs 2) = sp0 - 128 ->
PBUFW Wy mem -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H Wy) mem a) ->
(forall x : word, ~ X (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (INSTv + o_sec_mutex + k) = Some 0) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x322a0) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp0 - 128 - DEP_STK <= bv_unsigned x < sp0 - 128) -> ~ DZONE (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
DPOST z mem').
Local Ltac s_runS HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runS Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Lemma segT1 : forall (X : Z -> Prop), (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) S_TJ0 Wy c -> SRr tfibsegs Wy c (at_S Wy md1 X (PSR Wy SH2 RX) T_PD).
Proof.
intros X HXW c HR. pose proof SH_ok as (OK0 & OK1 & OK2). pose proof (PSR_stableS' Wy SH2 RX OK2 (RX_stableS RX RXt)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _). pose proof Nrange as NR. pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ.
unfold SEC_NMAX in Z1, Z8, NR. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2.
s_arm HR BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 6144) (SOff aMAP 0)).
{ clear - Z1 Z3 Z7 Z8 NR M1 M2 Hn MZ. arm_zevS. rewrite EaMAP, EaND, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
apply Z.ltb_ge. zlia. }
s_station HR T_J.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x321e0 (runto 0x321e0 T_J) HX HP2.
s_arm HR BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0).
{ clear - NR Hn MZ. arm_zevS. rewrite E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. land_lits.
rewrite Z.shiftr_div_pow2 by zlia. rewrite Z.add_0_r, (Z.div_small n (2 ^ 48)) by zlia. reflexivity. }
s_station HR T_K.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x72f3c T_PD HX HP2.
apply SRr_ret. exact HR.
Qed.
Definition DX (a : Z) : Prop := (sp0 - 128 - DEP_STK <= a < sp0 - 128) \/ DZONE a.
Hypothesis RXd : pstable DX RX.
Definition PD (z : Z) (m : word -> option byte) : Prop :=
exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H Wy) mem0 a -> apresent (w_H Wy) memD a) /\
(forall x : word, DZONE (bv_unsigned x) -> m x = memD x).
Lemma PD_rstable : forall z, rstable (PD z).
Proof.
intros z. split.
- intros m m' FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hw. exact (proj1 (DZONE_disj _ Hx) (WIN1R_WIN _ Hw)).
- intros m m' d len Hplace FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hin. exact (proj1 (DZONE_disj _ Hx) (place_WIN d len _ Hplace Hin)).
Qed.
Lemma PD_stableT : forall z, pstable WIN1T (PD z).
Proof.
intros z m m' FR (memD & D1' & D2 & D3). exists memD. split; [exact D1'|]. split; [exact D2|]. intros x Hx. rewrite FR; [exact (D3 x Hx)|].
intros Hw. exact (proj1 (DZONE_disj _ Hx) (WIN1T_WIN _ Hw)).
Qed.
Lemma PSR_stableS : forall sh R, Forall run_ok sh -> pstable WIN1S R -> pstable WIN1S (PSR Wy sh R).
Proof. intros sh R OK RS m m' FR [HP HQ]. split; [exact (PS_stable Wy sh OK m m' FR HP) | exact (RS m m' FR HQ)]. Qed.
Lemma PD_stableS : forall z, pstable WIN1S (PD z).
Proof. intros z m m' FR. apply (PD_stableT z m m'). intros x Hx. apply FR. intros Hw. exact (Hx (WIN1S_WIN1T _ Hw)). Qed.
Definition PDX (z : Z) (m : word -> option byte) : Prop := PD z m /\ RX m.
Lemma PDX_rstable : forall z, rstable (PDX z).
Proof. intros z. exact (rstable_and _ _ (PD_rstable z) RXs). Qed.
Lemma PDX_stableT : forall z, pstable WIN1T (PDX z).
Proof. intros z. exact (pstable_and _ _ _ (PD_stableT z) RXt). Qed.
Lemma PDX_stableS : forall z, pstable WIN1S (PDX z).
Proof. intros z. exact (pstable_and _ _ _ (PD_stableS z) (RX_stableS RX RXt)). Qed.
Definition dx_okb (s : option nat * Z * Z * Z * Z) : bool :=
match s with (b, lo, hi, _, _) =>
match b with
| Some 2%nat => (- 128 <=? lo) && (hi <=? 0)
| None => (0 <=? lo) && (hi <=? 0x5fd000) && ((hi <=? 0x179e08) || (0x5ca590 <=? lo))
| _ => skel_okb false s
end
end.
Lemma skel_apart_DX : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true ->
(forall a, base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ DX a /\ 0 <= a < 2 ^ 64).
Proof.
intros E' r HE Hs a Ha.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *;
[| apply andb_prop in Hs as [Hs _]; exact Hs].
destruct k as [|[|[|k]]]; try exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- AFSTACK) lo)) by (unfold AFSTACK; zlia). rewrite (proj2 (Z.leb_le hi 0) H2). reflexivity. }
split; [| exact (skel_u64 E' false r a HE SK Ha)].
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _).
pose proof Hidx as HI. pose proof Nrange as NR. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & QNB & QSB & NBS & SBS & CNB & CSB).
unfold zdisjoint in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB. cbn [fst snd] in TNB, TSB, QNB, QSB, NBS, SBS, CNB, CSB.
destruct Hmap_apart as (_ & _ & _ & _ & MNB & MSB & _). unfold zdisjoint in MNB, MSB. cbn [fst snd] in MNB, MSB.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DX, DZONE, DEP_STK, kNodesBlockSize, kStoreBlockSize, kHighMemBeg in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]]]; cbn [base_val] in Ha.
- unfold dx_okb in Hs. apply andb_prop in Hs as [_ H3]. apply Bool.orb_prop in H3 as [H3|H3]; apply Z.leb_le in H3;
clear - Ha A1 A2 H3 NBhi SBhi S1 T7 MZ; unfold AFSTACK in *; try unfold sp0 in *; zlia.
- rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2 in Ha. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1.
clear - Ha A1 A2 H1 NBS SBS S1 S3 T7 U2 MZ. unfold AFSTACK in *. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
pose proof stack_ivs as (DT & _). clear - Ha A1 A2 TNB TSB F1 F2 S1 S3 T7 U2 DT MZ. ceil; unfold kThreadObjSize, AFSTACK, ASAN_CEIL in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(unfold sHAV; zlia)), EaC in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - F7 F8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
pose proof stack_ivs as (_ & _ & DC & _). clear - Ha A1 A2 CNB CSB F7 F8 S1 S3 T7 U2 DC MZ. ceil; unfold AFSTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aMAP in Ha. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS. clear - Ha A1 A2 MNB MSB M1 M2 Z8 S1 S3 T7 U2 MS MZ.
ceil; unfold AFSTACK, ASAN_CEIL in *. try unfold sp0 in *. zlia.
- unfold aQS in Ha. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS in Ha. unfold w64 in Ha. unfold QSv in *. rewrite unsigned_lit_small in Ha by (clear - F9 F10 HI MZ; ceil; unfold ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *; try unfold Qb in *; zlia).
pose proof stack_ivs as (_ & _ & _ & SQ). clear - Ha A1 A2 QNB QSB F9 F10 HI S1 S3 T7 U2 SQ MZ. ceil; unfold AFSTACK, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL in Ha. rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL in Ha. unfold w64 in Ha. rewrite unsigned_lit_small in Ha by (clear - HB Hinst MZ; unfold INSTv in *; zlia).
clear - Ha A1 A2 HB Hinst NBhi SBhi S1 T7 MZ. unfold AFSTACK, INSTv in *. try unfold sp0 in *. zlia.
- unfold aINST in Ha. rewrite (HEn 11%nat ltac:(unfold sHAV; zlia)), E11 in Ha.
pose proof Hinst as HI0. clear - Ha A1 A2 HI0 NBhi SBhi S1 T7 MZ. unfold AFSTACK, INSTv in *. try unfold sp0 in *. zlia.
- unfold aSO in Ha. rewrite (HEn 13%nat ltac:(unfold sHAV; zlia)), E13 in Ha.
pose proof Hso as (SO1 & SO2 & _). clear - Ha A1 A2 SO1 SO2 NBS SBS S1 S3 T7 MZ. unfold AFSTACK, SOv in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma skel_apart_stk : forall (E' : env) r, env_agree sHAV E0 E' -> dx_okb (skel r) = true ->
base_val E' (YP09.r_base r) + YP09.r_hi r <= sp0 - AFSTACK \/ sp0 - 128 <= base_val E' (YP09.r_base r) + YP09.r_lo r.
Proof.
intros E' r HE Hs.
assert (SK : skel_okb false (skel r) = true).
{ destruct r as [[k|] lo hi wlo whi cs]; unfold skel, dx_okb in Hs |- *; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *;
[| apply andb_prop in Hs as [Hs _]; exact Hs].
destruct k as [|[|[|k]]]; try exact Hs. unfold skel_okb. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite (proj2 (Z.leb_le (- AFSTACK) lo)) by (unfold AFSTACK; zlia). rewrite (proj2 (Z.leb_le hi 0) H2). reflexivity. }
destruct HE as [HEn _]. pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
pose proof Hidx as HI. pose proof BSLv_range as HB. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _).
pose proof stack_ivs as (DT & _ & DC & SQ). destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
pose proof (u64_range (getr regs0 2)) as U2.
destruct r as [b lo hi wlo whi cs]. unfold skel in Hs, SK. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kMaxNumChunks in *.
destruct (skel_cases false b lo hi wlo whi SK) as [(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|[(-> & A1 & A2)|(Epb & -> & A1 & A2)]]]]]]]]]; cbn [base_val].
- left. clear - A1 A2 S1 T7 MZ. unfold AFSTACK in *. try unfold sp0 in *. zlia.
- right. rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2. unfold dx_okb in Hs. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. clear - H1 MZ. try unfold sp0 in *. zlia.
- rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT. unfold w64. rewrite unsigned_lit_small by (clear - F1 F2 MZ; numconst; try unfold T in *; zlia).
clear - A1 A2 DT MZ. unfold AFSTACK, kThreadObjSize in *. try unfold T in *. try unfold sp0 in *. zlia.
- rewrite (HEn 33%nat ltac:(unfold sHAV; zlia)), EaC. unfold w64. rewrite unsigned_lit_small by (clear - F7 F8 MZ; zlia).
clear - A1 A2 DC MZ. unfold AFSTACK in *. try unfold sp0 in *. zlia.
- unfold aMAP. rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP. unfold w64. rewrite unsigned_lit_small by (clear - M1 M2 Z8 MZ; zlia).
clear - A1 A2 MS M1 M2 Z8 S1 S3 MZ. unfold AFSTACK in *. try unfold sp0 in *. zlia.
- unfold aQS. rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS. unfold w64. unfold QSv in *. rewrite unsigned_lit_small by (clear - F9 F10 HI MZ; try unfold Qb in *; zlia).
clear - A1 A2 SQ HI MZ. unfold AFSTACK, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. try unfold sp0 in *. zlia.
- unfold aBSL. rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB Hinst MZ; unfold INSTv in *; zlia).
left. clear - A1 A2 HB Hinst S1 T7 MZ. unfold AFSTACK, INSTv in *. try unfold sp0 in *. zlia.
- unfold aINST. rewrite (HEn 11%nat ltac:(unfold sHAV; zlia)), E11.
left. pose proof Hinst as HI0. clear - A1 A2 HI0 S1 T7 MZ. unfold AFSTACK, INSTv in *. try unfold sp0 in *. zlia.
- unfold aSO. rewrite (HEn 13%nat ltac:(unfold sHAV; zlia)), E13.
right. pose proof Hso as (SO1 & _). clear - A1 SO1 MZ. unfold SOv in *. try unfold sp0 in *. zlia.
- discriminate Epb.
Qed.
Lemma at_S_depot : forall (X : Z -> Prop), (forall a, X a -> WIN a \/ QR a) -> (forall a, WIN a -> X a) ->
forall c, at_S Wy md1 X (PSR Wy SH2 RX) T_PD Wy c ->
SRr tfibsegs Wy c (fun W2 c2 => exists z, at_S Wy md1 (fun a => X a \/ DX a) (PSR Wy SH2 (PDX z)) T_2 W2 c2).
Proof.
intros X HXQ HXW c HR. destruct HR as (EW & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). clear EW. pose proof (proj1 HE) as HEn.
pose proof Hwx_tfa as Hwx. pose proof Hsp as (Hlo & Hbot & Hhi & Hal). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (u64_range (getr regs0 2)) as Usp.
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wy) E' _ _ HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
lazymatch type of Hshape with _ = mkst _ (Z_to_bv 64 (ss_pc ?s)) _ _ => let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p in Hshape end. rewrite Hshape.
rreg HS (2%bv : bv 5) R2. rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2 in R2.
eapply SRr_mono.
{ apply (D1w X (ms_regs ms) (ms_mem ms) _ HXQ).
- rreg HS (10%bv : bv 5) R; rewrite R, (HEn 12%nat ltac:(unfold sHAV; zlia)), (Er 12 12%bv eq_refl). unfold BPv. rewrite Z_to_bv_bv_unsigned. reflexivity.
- rreg HS (11%bv : bv 5) R; rewrite R, (HEn 36%nat ltac:(unfold sHAV; zlia)). reflexivity.
- rreg HS (3%bv : bv 5) R; rewrite R, (HEn 3%nat ltac:(unfold sHAV; zlia)). exact (Er 3 3%bv eq_refl).
- rreg HS (4%bv : bv 5) R; rewrite R. reflexivity.
- rreg HS (1%bv : bv 5) R; rewrite R. reflexivity.
- rewrite R2. clear - Hlo Hhi T4 T7 Usp. rewrite unsigned_lit_small by (unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AFSTACK, kHighMemEnd, kHighMemBeg in *; unfold sp0 in *; zlia). unfold sp0; zlia.
- exact (proj1 (proj1 HPm)).
- exact PRS.
- exact MEQ.
-
destruct (st_ok_mem_ok tfibsegs E' _ _ HS) as (_ & ROK & _).
set (RMUT := YP09.mkRegion (Some aINST) o_sec_mutex (o_sec_mutex + 4) o_sec_mutex (o_sec_mutex + 4)
[YP09.mkChunk o_sec_mutex (CVal 1 (SLit 0)); YP09.mkChunk (o_sec_mutex + 1) (CVal 1 (SLit 0));
YP09.mkChunk (o_sec_mutex + 2) (CVal 2 (SLit 0))]).
assert (HIN : In RMUT (ss_mem T_PD)) by (subst RMUT; vm_compute; repeat (first [left; reflexivity | right])).
pose proof (proj1 (Forall_forall _ _) ROK RMUT HIN) as (_ & _ & _ & RC). subst RMUT. cbn [YP09.r_chunks YP09.r_base base_val] in RC. unfold aINST in RC. rewrite (HEn 11%nat ltac:(unfold sHAV; zlia)), E11 in RC.
apply Forall_cons_iff in RC as [_ RC]. apply Forall_cons_iff in RC as [C1 RC]. apply Forall_cons_iff in RC as [C2 _].
intros k Hk. unfold aview. cbn [restrict ms_mem].
assert (Hcase : k = 1 \/ k = 2 \/ k = 3) by zlia. destruct Hcase as [-> | [-> | ->]].
+ destruct (C1 0 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (INSTv + o_sec_mutex + 1) with (bv_unsigned (getr regs0 11) + (o_sec_mutex + 1) + 0) by (unfold INSTv; zlia). rewrite Hm. rewrite <- Hb. vm_compute. reflexivity.
+ destruct (C2 0 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (INSTv + o_sec_mutex + 2) with (bv_unsigned (getr regs0 11) + (o_sec_mutex + 2) + 0) by (unfold INSTv; zlia). rewrite Hm. rewrite <- Hb. vm_compute. reflexivity.
+ destruct (C2 1 ltac:(cbn; zlia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte restrict ms_mem] in Hb, Hm.
replace (INSTv + o_sec_mutex + 3) with (bv_unsigned (getr regs0 11) + (o_sec_mutex + 2) + 1) by (unfold INSTv; zlia). rewrite Hm. rewrite <- Hb. vm_compute. reflexivity. }
intros W' c' Hle (-> & z & regs2 & mem2 & mat2 & -> & HP & Hfr & Hpr & HDP). exists z.
set (mem := ms_mem ms) in *.
assert (Hfr' : forall x : word, ~ DX (bv_unsigned x) -> mem2 x = mem x) by (intros x Hx; apply Hfr; unfold DX in Hx; tauto).
lazymatch type of HS with st_ok _ _ ?ss ?ms0 =>
let m := eval vm_compute in (ss_mem ss) in
lazymatch m with ?rq :: ?rm :: ?rb :: ?r1 :: ?rest =>
pose proof (st_ok_after_call tfibsegs sD1 E' ss ms0 regs2 (mrestrict (w_H Wy) mem2) (rq :: rm :: rb :: trim_lo r1 (-128) :: rest) 0x322a0 HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|];
apply submem_keep; [apply subregion_trim_lo | apply submem_refl])
ltac:(vm_compute; reflexivity) HP) as HS1;
let rsv := eval vm_compute in (rq :: rm :: rb :: trim_lo r1 (-128) :: rest) in
change (rq :: rm :: rb :: trim_lo r1 (-128) :: rest) with rsv in HS1;
let ss2 := eval vm_compute in (ss_after_call ss rsv sD1 0x322a0) in
change (ss_after_call ss rsv sD1 0x322a0) with ss2 in HS1
end
end.
cbn [ms_mem restrict] in HS1. fold mem in HS1.
lazymatch type of HS1 with Forall _ ?rs -> _ =>
assert (KEPT : Forall (region_kept tfibsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem2)) rs);
[ apply Forall_forall; intros r Hr;
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => dx_okb (skel r)) rs = true) r Hr) as CK; cbn beta in CK;
apply (kept_of_frame2 (w_H Wy) E' mem mem2 DX r Hfr');
[ exact (skel_apart_DX E' r HE CK)
| intros a Ha; pose proof (region_wf_facts r (regions_wf_In rs r ltac:(vm_compute; reflexivity) Hr)) as (_ & WW & _); apply (skel_apart_DX E' r HE CK); clear - Ha WW; zlia ]
| specialize (HS1 KEPT); clear KEPT ]
end.
assert (PRES2 : forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H Wy) mem2 a) by (intros a Ha; apply Hpr, PRS, Ha).
set (En3 := havoc E' sD1 (map (getr regs2) CLOB)) in HS1.
assert (HE3 : env_agree sHAV E0 En3) by (exact (env_agree_havoc_ge sHAV sD1 E0 E' _ ltac:(unfold sHAV, sD1; zlia) HE)).
pose proof (proj1 HE3) as HEn3.
apply (st_ok_add_region _ _ _ R_scr2) in HS1;
[ | reflexivity
| unfold YP09.region_ok, R_scr2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
rewrite (HEn3 2%nat ltac:(unfold sHAV; zlia)), E2;
split; [clear - Hlo T7; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AFSTACK, kHighMemBeg in *; unfold sp0 in *; zlia|]; split; [clear - Usp; zlia|]; split;
[ intros o Ho; apply apresent_writable_off; [off_by ltac:(clear - Ho Hlo T7 Usp; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, AFSTACK, TFIB_IMG_END, kHighMemBeg in *; unfold sp0 in *; zlia) | apply PRES2; clear - Ho; unfold AFSTACK in *; zlia] | apply Forall_nil ]
| apply all_disjoint_of_forall; intros r' Hr';
lazymatch type of Hr' with In _ ?l =>
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun r => dx_okb (skel r)) l = true) r' Hr') as CK1; cbn beta in CK1 end;
unfold extent_disjoint, R_scr2; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn3 2%nat ltac:(unfold sHAV; zlia)), E2;
pose proof (skel_apart_stk En3 r' HE3 CK1) as AP; clear - AP; unfold sp0 in *; zlia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
lazymatch type of HS1 with st_ok _ _ ?ss _ => replace ss with T_2 in HS1 by (vm_compute; reflexivity) end.
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 0x322a0) mem2 (seg_rom tfibsegs)), mat2, En3.
split; [rewrite wvb_collapse; reflexivity|]. split; [exact HE3|]. split; [rewrite restrict_mkst_fx; exact HS1|].
split. { intros x Hx. cbn [ms_mem mkst]. rewrite Hfr' by (intros Hd; apply Hx; right; exact Hd). apply MEQ. intros HX'; apply Hx; left; exact HX'. }
split; [exact PRES2|].
destruct HPm as [(HB & HM & HSH & HRs) HRX]. cbn [ms_mem mkst].
assert (NDX : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> ~ DX a).
{ intros a Ha [Hs|Hd].
- apply (runs_not_stack a Ha). unfold DEP_STK, AFSTACK in *. zlia.
- apply (proj1 (DZONE_disj a Hd)). apply (place_WIN a 1 a); [clear - Ha; zlia | zlia]. }
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
assert (U64R : forall a, (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. clear - Ha M1 M2 SM1 SM2 MZ. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in *. zlia. }
split; [split; [|split; [|split]]|].
- intros i Hi. eapply val_mem_frame; [|exact (HB i Hi)]. intros kk Hkk. apply Hfr'. pose proof tr_length as LEN. pose proof Hbp as (BP1 & BP2 & _).
rewrite unsigned_lit_small by (clear - Hi Hkk LEN BP1 BP2 Hlo T4 T7 MZ; unfold AFSTACK, kHighMemBeg, kHighMemEnd in *; zlia).
intros [Hs|Hd]; [clear - Hs Hi Hkk LEN BP1 MZ; unfold DEP_STK in *; zlia|].
apply (DZONE_disj_hi _ Hd). clear - Hi Hkk LEN BP1 BP2 MZ. zlia.
- intros a Ha. apply Hpr. exact (HM a Ha).
- intros a Ha. apply Hpr. exact (HSH a Ha).
- pose proof SH_ok as (_ & _ & OK2). apply Forall_forall. intros r Hr a Ha. pose proof (proj1 (Forall_forall _ _) OK2 r Hr) as RO.
assert (PL : (mb + 6144 <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8)) by (unfold run_ok in RO; clear - RO Ha MZ; zlia).
unfold w64. rewrite Hfr' by (rewrite (U64R a PL); exact (NDX a PL)). exact (proj1 (Forall_forall _ _) HRs r Hr a Ha).
- split; [| exact (RXd mem mem2 Hfr' HRX)].
exists mem2. split; [exact HDP|]. split; [|intros x _; reflexivity].
intros a Hd Hp0. apply Hpr. apply (apresent_same (w_H Wy) mem0); [|exact Hp0]. apply MEQ.
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). unfold zdisjoint in QNB, QSB. cbn [fst snd] in QNB, QSB.
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hres as [HRS _].
rewrite unsigned_lit_small by (clear - Hd NBhi SBhi MZ; unfold DZONE in *; numconst; zlia).
intros HXa. destruct (HXQ a HXa) as [Hw|Hq]; [exact (proj1 (DZONE_disj a Hd) Hw)|].
unfold QR in Hq. pose proof Hidx as HI9. clear - Hd Hq QNB QSB F9 HRS HI9 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, DZONE, kHighMemBeg, kNodesBlockSize, kStoreBlockSize, kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. try unfold Qb in *. zlia.
Qed.
Definition SH3 : list (Z * Z * Z) :=
[(SMv + 512, SMv + 768, 250); (SHBv + ENDv / 8, SMv + MSv / 8, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + ENDv / 8, 0)].
Definition SH4 : list (Z * Z * Z) :=
[(SHBv + UEv / 8, SMv + MSv / 8, 250); (SMv + 512, SMv + 768, 250); (SMv, SMv + 512, 250); (SMv + 768, SHBv + UEv / 8, 0)].
Lemma shadow_marks :
SHBv + ENDv / 8 = SMv + 512 + NDv / 8 /\ SHBv + UEv / 8 = SMv + 768 + R8v / 8 /\ SMv + MSv / 8 = SHBv + UEv / 8 + RLv / 8 /\
NDv / 8 = R8v / 8 + 512 /\ 8065 <= R8v / 8 <= 2 ^ 27 /\ 256 <= RLv / 8 /\ SMv = SHBv + mb / 8 /\ MSv / 8 = NDv / 8 + 512 + TLv / 8 /\ 0 <= TLv / 8.
Proof.
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). unfold SEC_NMAX in Z1, Z8.
clear - M1 M3 U5 E6 UE7 MT MU Z1 Z2 Z7 Z8 Z9 Z10 Z11 Z13 MZ. unfold AGjm.SMv, AGjm.SHBv.
rewrite E6, UE7 in *. rewrite U5 in *. rewrite Z7 in *.
replace RLv with (MSv - R8v - 6144) in * by zlia. replace TLv with (MSv - R8v - 8192) in * by zlia.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. apply Z.mod_divide in Z2 as [q Hq]; [|zlia]. apply Z.mod_divide in Z9 as [w Hw]; [|zlia].
rewrite Hu, Hq, Hw in *.
replace (u * 4096 + 6144 + q * 8 + 2048) with ((u * 512 + 1024 + q) * 8) by zlia. replace (u * 4096 + 6144 + q * 8) with ((u * 512 + 768 + q) * 8) by zlia.
replace (w * 4096) with ((w * 512) * 8) by zlia. replace (q * 8 + 4096) with ((q + 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 6144) with ((w * 512 - q - 768) * 8) by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia.
replace ((w * 512) * 8 - q * 8 - 8192) with ((w * 512 - q - 1024) * 8) by zlia.
rewrite !Z_div_mult by zlia. repeat split; zlia.
Qed.
Lemma SH34_ok : Forall run_ok SH3 /\ Forall run_ok SH4.
Proof.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). clear - A1 A2 A3 A4 A5 A6 A7 A8 A9.
unfold SH3, SH4, run_ok. repeat split; repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; zlia.
Qed.
Section T2.
Variables (X : Z -> Prop) (z : Z).
Hypothesis HXW : forall a, WIN a -> X a.
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
Lemma segT2b : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_N W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof SH34_ok as [OK3 OK4]. pose proof (PDX_rstable z) as RS.
pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2. pose proof (PSR_stableS SH3 (PDX z) OK3 (PDX_stableS z)) as HP3. pose proof (PSR_stableS SH4 (PDX z) OK4 (PDX_stableS z)) as HP4.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR.
unfold SEC_NMAX in Z1, Z8, NR. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd in M1, M2, SM1, SM2.
pose proof shadow_marks as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x542b4 T_L3 HX HP2.
s_ladder s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x98e24 T_L3l T_L3lo T_L3h T_L3h2 T_L3h3 T_L3hi T_M3 sL3 CLOB_L HX HP2.
s_memsetR HR T_P3 sM3 constr:(SMv + 512) 256 250 0x32378 OK2 RS.
{ clear - M1 M2 M3 Z8 A7 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaMAP. unfold w64, AGjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu in *. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite Z_div_mult by zlia.
rewrite A7. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z_div_mult by zlia. zcanon_simp. zlia. }
{ clear - M1 M2 M3 Z8 MZ. U_zevS. rewrite EaMAP. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in M3 as [u Hu]; [|zlia]. rewrite Hu.
replace (u * 4096 + 6136) with ((u * 512 + 767) * 8) by zlia. replace (u * 4096 + 4096) with ((u * 512 + 512) * 8) by zlia. rewrite !Z_div_mult by zlia.
zcanon_simp. zlia. }
{ right. clear - A1 A4 A5 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH3 (PDX z) T_P3) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH2 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SHBv + ENDv / 8 <? SMv + 512) = false) by (clear - A1 A4 A5 MZ; apply Z.ltb_ge; zlia).
assert (G2 : (SMv + 512 + 256 <? SMv + MSv / 8) = true) by (clear - A4 A5 A8 A9 MZ; apply Z.ltb_lt; zlia).
assert (G3 : (SMv <? SMv + 512) = true) by (apply Z.ltb_lt; zlia).
assert (G4 : (SMv + 512 + 256 <? SMv + 512) = false) by (apply Z.ltb_ge; zlia).
assert (G5 : (SMv + 512 <? SMv + 512) = false) by (apply Z.ltb_irrefl).
assert (G6 : (SMv + 512 + 256 <? SHBv + ENDv / 8) = true) by (clear - A1 A4 A5 MZ; apply Z.ltb_lt; zlia).
rewrite G1, G2, G3, G4, G5, G6 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.max_l in C1 by (clear - A1 A4 A5 MZ; zlia). rewrite Z.min_l in C2 by zlia. rewrite Z.max_r in C3 by zlia.
replace (SMv + 512 + 256) with (SMv + 768) in B1 by zlia.
unfold SH3. apply Forall_cons; [exact B1|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [|apply Forall_nil].
intros a Ha. apply C3. cbn [fst snd] in *. zlia. }
s_pin HR (22%bv : bv 5) (SOff aUE 0).
{ clear - M1 M2 M3 Z8 Z1 Z2 Z3 NR UE7 U5 Hn MZ. pin_zevS. rewrite EaUE, EaMAP, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change (zcanon (-8)) with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. rewrite UE7, U5.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)) as D8. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)) as B8. unfold R8v in *.
apply Z.mod_divide in M3 as [u Hu]; [|zlia].
replace ((n + 6151 + (mb + 0)) mod 8) with ((n + 7) mod 8); [zcanon_simp; zlia|].
rewrite Hu. replace (n + 6151 + (u * 4096 + 0)) with ((n + 7) + (768 + u * 512) * 8) by zlia. rewrite Z_mod_plus_full. reflexivity. }
s_pin HR (8%bv : bv 5) (SOff aMS (-4096)).
{ clear - Z1 Z7 Z8 Z9 Z10 MZ. pin_zevS. rewrite EaMS, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_neg_pow2_u64 by zlia. change (2 ^ 12) with 4096.
pose proof (Z.div_mod (NDv + 4095) 4096 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound (NDv + 4095) 4096 ltac:(zlia)) as MB.
unfold AGjm.MSv in *. zcanon_simp. zlia. }
s_station HR T_P4.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32388 (runto 0x32388 T_P4) HX HP3.
s_pin HR (11%bv : bv 5) (SOff aRL 0).
{ clear - M1 M2 Z8 Z1 Z13 MU UE7 U5 MZ. pin_zevS. rewrite EaRL, EaMS, EaMAP, EaUE. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (RLv + 0)), (zcanon_id (MSv + 0)), (zcanon_id (mb + 0)), (zcanon_id (UEv + 0)), (zcanon_id (MSv + 0 + (mb + 0))) by (unfold M64; zlia).
unfold zcanon, M64. rewrite Zmult_mod_idemp_r. rewrite Zplus_mod_idemp_r.
replace (MSv + 0 + (mb + 0) + (UEv + 0) * 18446744073709551615) with ((RLv + 0) + UEv * 2 ^ 64) by zlia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. zlia. }
s_station HR T_P5.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x542b4 T_L4 HX HP3.
s_ladder s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x98e24 T_L4l T_L4lo T_L4h T_L4h2 T_L4h3 T_L4hi T_M4 sL4 CLOB_L HX HP3.
s_memsetR HR T_P6 sM4 constr:(SHBv + UEv / 8) constr:(RLv / 8) 250 0x3238c OK3 RS.
{ clear - M1 M2 Z8 Z1 UE7 U5 A2 A7 A5 SM1 MZ. U_zevS. rewrite (eq_refl : ew E0 47 = w64 SHBv), EaUE. unfold w64, AGjm.SHBv in *. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
pose proof (Z.div_pos UEv 8 ltac:(zlia) ltac:(zlia)). pose proof (Z.div_lt_upper_bound UEv 8 (2 ^ 61) ltac:(zlia) ltac:(zlia)). zcanon_simp. zlia. }
{ clear - M1 M2 Z8 Z1 Z13 Z14 UE7 UE9 U5 A2 A3 A5 A6 A7 MZ. U_zevS. rewrite EaUE, EaRL. unfold w64. rewrite !unsigned_lit_small by zlia.
zcanon_simp. land_lits. rewrite !Z.shiftr_div_pow2 by zlia. change (2 ^ 3) with 8.
apply Z.mod_divide in UE9 as [q Hq]; [|zlia]. apply Z.mod_divide in Z14 as [t Ht]; [|zlia]. rewrite Hq, Ht in *.
replace (q * 8 + -8 + (t * 8 + 0)) with ((q + t - 1) * 8) by zlia. replace (q * 8 + 0) with (q * 8) by zlia. rewrite !Z_div_mult in * by zlia.
zcanon_simp. zlia. }
{ right. clear - A2 A3 A5 A6 A4 A8 A9 MZ. zlia. }
apply (PSR_runs Wy md1 X _ SH4 (PDX z) T_P6) in HR.
2:{ intros m HF. pose proof (Forall_inv HF) as B1. pose proof (Forall_inv_tail HF) as B2'. clear HF.
unfold cut, SH3 in B2'. cbn [flat_map app] in B2'. unfold cut1 in B2'. cbn [fst snd] in B2'.
assert (G1 : (SMv + 512 <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G2 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 768) = false) by (clear - A2 A5 A6 MZ; apply Z.ltb_ge; zlia).
assert (G3 : (SHBv + ENDv / 8 <? SHBv + UEv / 8) = false) by (clear - A1 A2 A4 MZ; apply Z.ltb_ge; zlia).
assert (G4 : (SHBv + UEv / 8 + RLv / 8 <? SMv + MSv / 8) = false) by (clear - A3 MZ; apply Z.ltb_ge; zlia).
assert (G5 : (SMv <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G6 : (SHBv + UEv / 8 + RLv / 8 <? SMv + 512) = false) by (clear - A2 A5 A6 MZ; apply Z.ltb_ge; zlia).
assert (G7 : (SMv + 768 <? SHBv + UEv / 8) = true) by (clear - A2 A5 MZ; apply Z.ltb_lt; zlia).
assert (G8 : (SHBv + UEv / 8 + RLv / 8 <? SHBv + ENDv / 8) = false) by (clear - A1 A3 A4 A8 A9 MZ; apply Z.ltb_ge; zlia).
rewrite G1, G2, G3, G4, G5, G6, G7, G8 in B2'. cbn [app] in B2'.
pose proof (Forall_inv B2') as C1. pose proof (Forall_inv (Forall_inv_tail B2')) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail B2'))) as C3. clear B2'.
rewrite Z.min_l in C1 by (clear - A2 A5 MZ; zlia). rewrite Z.min_l in C2 by (clear - A2 A5 MZ; zlia). rewrite Z.min_r in C3 by (clear - A1 A2 A4 MZ; zlia).
rewrite <- A3 in B1. unfold SH4. apply Forall_cons; [exact B1|]. apply Forall_cons; [exact C1|]. apply Forall_cons; [exact C2|]. apply Forall_cons; [exact C3 | apply Forall_nil]. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x32398 (runto 0x32398 T_P6) HX HP4.
s_pin HR (22%bv : bv 5) (SOff aN8DS 0).
{ clear - NR Hn Z4 MZ. pin_zevS. rewrite EaN8D, E10, Hn. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
change (zcanon 281474976710648) with (2 ^ 48 - 8). rewrite land_m8_48 by zlia. unfold N8D in *.
pose proof (Z.div_mod n 8 ltac:(zlia)). pose proof (Z.mod_pos_bound n 8 ltac:(zlia)). rewrite Z.add_0_r. zcanon_simp. zlia. }
s_station HR T_P7.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x542b4 T_L5 HX HP4.
s_ladderW s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x54504 T_L5l T_L5lo T_L5h T_L5h2 T_L5h3a T_L5h3 T_L5hi T_R sL5 CLOB_Lt HX HP4.
apply SRr_ret. exact HR.
Qed.
Lemma segT2 : forall W' c, at_S Wy md1 X (PSR Wy SH2 (PDX z)) T_2 W' c -> SRr tfibsegs W' c (at_S Wy md1 X (PSR Wy SH4 (PDX z)) T_R).
Proof.
intros W1 c HR. pose proof SH_ok as (_ & _ & OK2). pose proof (PSR_stableS SH2 (PDX z) OK2 (PDX_stableS z)) as HP2.
assert (HX : forall a, WIN1S a -> X a) by (intros a Ha; apply HXW, WIN1S_WIN, Ha).
pose proof map_facts as (M1 & M2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in M1, M2. unfold SEC_NMAX in Z8.
pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in F3, F4, F5, F6.
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322d4 T_M0 HX HP2.
destruct Hmap_apart as (_ & _ & MP & _). unfold zdisjoint in MP. cbn [fst snd] in MP. unfold kPrimResvSize in MP.
destruct MP as [MP|MP].
- s_arm HR BC_LTU true (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp. apply Z.ltb_lt. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x3230c T_Ma HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(unfold sHAV, sGA; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. exact (segT2b _ _ HR).
- s_arm HR BC_LTU false (SOff aMAP 4096) (SOff aSB 0).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp. apply Z.ltb_ge. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x322e4 (runto 0x322e4 (arm BC_LTU false (SOff aMAP 4096) (SOff aSB 0) T_M0)) HX HP2.
s_arm HR BC_GEU true (SOff aMAP 4096) (SOff aSB 137438953472).
{ clear - MP M1 M2 Z8 F3 F4 F5 F6 MZ. arm_zevS. rewrite EaMAP, EaSB. unfold w64. rewrite !unsigned_lit_small by (try unfold SB in *; zlia). zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity|]. try unfold SB in *. zlia. }
s_runS HR tfibtbl_rtA tfibtbl_rtA_ok 0x3230c T_Mb HX HP2.
lazymatch type of HR with at_S ?Wx ?md ?X0 ?P ?ss ?W' ?c' =>
pose proof (at_S_forget Wx md X0 P ss W' c' sGA [11]%bv HR ltac:(unfold sHAV, sGA; zlia) eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HR2; clear HR; rename HR2 into HR end.
s_noconds HR. s_station HR T_N. exact (segT2b _ _ HR).
Qed.
End T2.
End g.
End f.
