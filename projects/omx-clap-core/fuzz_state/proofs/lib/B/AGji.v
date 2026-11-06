(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGji.v (a working branch 86aa4177b94, file sha256 1ae2461bcdeb) onto omx-clap-core/fuzz_state's asan-ubsan image (fuzz_state.asan-ubsan, pinned sha256 5ac5ce0954f8; addresses read from its unstripped build b1566a1ca816); module paths changed; its 17 image addresses moved by code-verified function pairs (24 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YE3d YB1q YFhy AGhy AGhz AGi0 AGi4 AGi9 YB1h AGjm AGid AGjh.
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
Hypothesis Hinst : 0x9f000 <= INSTv /\ INSTv + 0xe60 <= 0x12a6a0 /\ INSTv mod 8 = 0.
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
Local Abbreviation PBUF := (@AGjh.PBUF W regs0 tr).
Local Abbreviation PBUF_stableP := (@AGjh.PBUF_stableP _ W ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@AGjh.PBUF_stableM _ W ly regs0 n tr idx res mb LY IMG Hsp Htrlen Hbp Hinst Nrange Hidx Hres Hmap).
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
RUN HR tbl tblok 0x5450c Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54364 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5450c Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5454c Sh3 HX HP;
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
RUN HR tbl tblok 0x5450c Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54364 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5450c Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54548 Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x5454c Sh3 HX HP;
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
RUN HR tbl tblok 0x32484 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x32488 Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Lemma seg1 : forall W' c', at_S W md0 WINP PBUF S_1 W' c' -> SRr tfibsegs W' c' (at_N W md0 WINP PBUF S_N).
Proof.
clearP. intros W1 c1 HR. pose proof PBUF_stableP as HP. pose proof WIN1P_WINP as HX.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR. unfold SEC_NMAX in Z1, Z8, NR.
assert (ZR8 : zev (rho_of E0) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) = R8v).
{ clear - Hn Z1 Z2 Z3 NR.
cbn [zev zalu_raw]. unfold rho_of. rewrite E10, Hn. unfold w64. rewrite unsigned_lit_small by zlia.
rewrite (zcanon_id (n + 7)) by (unfold M64; zlia). rewrite (zcanon_id 18446744073709551608) by (unfold M64; zlia).
change 18446744073709551608 with (2 ^ 64 - 8). rewrite land_m8_64 by zlia. unfold R8v.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)). rewrite zcanon_id; unfold M64; zlia. }
s_runP HR tfibtbl_rtA tfibtbl_rtA_ok 0x3213c S_B0 HX HP.
s_pin HR (10%bv : bv 5) (SOff aR8 0).
{ clear - ZR8 Z1. pin_zevS.
change (zcanon (bv_unsigned (ew E0 38) + 0) = zcanon (zcanon (Z.land (zcanon (bv_unsigned (ew E0 10) + 7)) (zcanon 18446744073709551608)) + zcanon 0)) .
change (zcanon (Z.land (zcanon (bv_unsigned (ew E0 10) + 7)) (zcanon 18446744073709551608))) with (zev (rho_of E0) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608))).
rewrite ZR8, EaR8. unfold w64. rewrite unsigned_lit_small by zlia. zcanon_simp. change (zcanon 0) with 0. zcanon_simp. zlia. }
s_pin HR (11%bv : bv 5) (SLit 0).
{ clear - ZR8 Z1 Z2. pin_zevS.
change (zcanon 0 = zcanon (Z.land (zcanon (zev (rho_of E0) (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) + zcanon 0)) (zcanon 7))).
rewrite ZR8. change (zcanon 0) with 0. change (zcanon 7) with 7. rewrite Z.add_0_r. zcanon_simp. rewrite land_7_mod by zlia. rewrite Z2. reflexivity. }
s_station HR S_B.
s_runP HR tfibtbl_rtA tfibtbl_rtA_ok 0x32178 S_C0 HX HP.
s_pin HR (19%bv : bv 5) (SOff aND 0).
{ clear - Z1 Z7. pin_zevS. rewrite EaND, EaR8. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp. zlia. }
s_station HR S_C.
s_runP HR tfibtbl_rtA tfibtbl_rtA_ok 0x3662c S_D0 HX HP.
s_arm HR BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8).
{ clear - Z1 Z7. arm_zevS. rewrite EaND. unfold w64. rewrite unsigned_lit_small by zlia. zcanon_simp.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by zlia. change (zcanon 8) with 8. rewrite zcanon_id by (unfold M64; zlia).
rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity | zlia]. }
s_station HR S_D.
s_runP HR tfibtbl_rtA tfibtbl_rtA_ok 0x36958 S_E0 HX HP.
s_pin HR (18%bv : bv 5) (SOff aMS 0).
{ clear - Z1 Z7 Z8. pin_zevS. rewrite EaMS, EaND. unfold w64. rewrite !unsigned_lit_small by zlia.
rewrite (zcanon_id (NDv + 4095)) by (unfold M64; zlia). change (zcanon 18446744073709547520) with (2 ^ 64 - 2 ^ 12).
rewrite land_neg_pow2_u64 by zlia. change (zcanon 4096) with 4096. change (zcanon 0) with 0.
pose proof (Z.div_mod (NDv + 4095) 4096 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound (NDv + 4095) 4096 ltac:(zlia)) as MB.
change (2 ^ 12) with 4096. unfold MSv in *. zcanon_simp. zlia. }
s_arm HR BC_GEU true (SOff aMS 0) (SOff aND 0).
{ clear - Z1 Z7 Z8 Z10. arm_zevS. rewrite EaMS, EaND. unfold w64. rewrite !unsigned_lit_small by zlia. zcanon_simp.
rewrite (proj2 (Z.ltb_ge _ _)); [reflexivity | zlia]. }
s_station HR S_E.
s_runP HR tfibtbl_rtA tfibtbl_rtA_ok 0x7ffffff0 S_G HX HP.
s_ecallP HR tfibtbl_rtC tfibtbl_rtC_ok S_N HX HP.
Qed.
End f.
End d.
