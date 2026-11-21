(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFjr.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFjr.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0s_w YG0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0l AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1w AE3d AB1q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AB1h_w AFjm_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA09_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFid_w AFie_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFjv_w AFjw_w AFjx_w AFjh_w AFjn_w AFjo_w AFjk_w AFjp_w AFjq_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Local Abbreviation R8v := (@AFjm_w.R8v n).
Local Abbreviation N8D := (@AFjm_w.N8D n).
Local Abbreviation NDv := (@AFjm_w.NDv n).
Local Abbreviation MSv := (@AFjm_w.MSv n).
Local Abbreviation SHBv := (@AFjm_w.SHBv).
Local Abbreviation QSv := (@AFjm_w.QSv ly idx).
Local Abbreviation Kv := (@AFjm_w.Kv mb).
Local Abbreviation Uv := (@AFjm_w.Uv mb).
Local Abbreviation ENDv := (@AFjm_w.ENDv n mb).
Local Abbreviation TLv := (@AFjm_w.TLv n).
Local Abbreviation UEv := (@AFjm_w.UEv n mb).
Local Abbreviation RLv := (@AFjm_w.RLv n).
Local Abbreviation SMv := (@AFjm_w.SMv mb).
Local Abbreviation PBv := (@AFjm_w.PBv n mb).
Local Abbreviation LGv := (@AFjm_w.LGv n).
Local Abbreviation BSLv := (@AFjm_w.BSLv n).
Local Abbreviation tr := (@AFjm_w.tr ly regs0 ch).
Local Abbreviation XW := (@AFjm_w.XW ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E0 := (@AFjm_w.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation Er := (@AFjm_w.Er ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E1 := (@AFjm_w.E1 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E2 := (@AFjm_w.E2 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E4 := (@AFjm_w.E4 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E8 := (@AFjm_w.E8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation E10 := (@AFjm_w.E10 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaT := (@AFjm_w.EaT ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaC := (@AFjm_w.EaC ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSB := (@AFjm_w.EaSB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTOP := (@AFjm_w.EaTOP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaR8 := (@AFjm_w.EaR8 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQ := (@AFjm_w.EaQ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRES := (@AFjm_w.EaRES ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaNCH := (@AFjm_w.EaNCH ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMS := (@AFjm_w.EaMS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaMAP := (@AFjm_w.EaMAP ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaEND := (@AFjm_w.EaEND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSHB := (@AFjm_w.EaSHB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaTL := (@AFjm_w.EaTL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaQS := (@AFjm_w.EaQS ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaBSL := (@AFjm_w.EaBSL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaSM := (@AFjm_w.EaSM ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaUE := (@AFjm_w.EaUE ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaND := (@AFjm_w.EaND ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaRL := (@AFjm_w.EaRL ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaN8D := (@AFjm_w.EaN8D ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation EaPB := (@AFjm_w.EaPB ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Local Abbreviation mod0_of_mul := (@AFjm_w.mod0_of_mul).
Local Abbreviation size_facts := (@AFjm_w.size_facts n Nrange).
Local Abbreviation tr_length := (@AFjm_w.tr_length ly regs0 ch idx res Hidx).
Local Abbreviation high_facts := (@AFjm_w.high_facts _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation stack_ivs := (@AFjm_w.stack_ivs _ ly regs0 idx res LY Hsp Hidx Hres).
Local Abbreviation HCX := (@AFjm_w.HCX _ ly LY).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Local Abbreviation map_facts := (@AFjm_w.map_facts _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_zone := (@AFjm_w.map_zone _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_zoneN := (@AFjm_w.map_zoneN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation map_in_band := (@AFjm_w.map_in_band _ ly regs0 n idx res mb Nrange Hidx Hmap).
Local Abbreviation map_off_img := (@AFjm_w.map_off_img _ n mb Hmap).
Local Abbreviation WINT := (@AFjm_w.WINT ly).
Local Abbreviation WINI := (@AFjm_w.WINI n).
Local Abbreviation WINM := (@AFjm_w.WINM ly n idx mb).
Local Abbreviation WIN := (@AFjm_w.WIN ly regs0 n idx mb).
Local Abbreviation WINN := (@AFjm_w.WINN ly regs0).
Local Abbreviation WINP := (@AFjm_w.WINP ly regs0 n).
Local Abbreviation WINP_WIN := (@AFjm_w.WINP_WIN ly regs0 n idx mb).
Local Abbreviation WIN1P := (@AFjm_w.WIN1P ly regs0 n).
Local Abbreviation WIN1 := (@AFjm_w.WIN1 ly regs0 n idx mb).
Local Abbreviation WIN1P_WINP := (@AFjm_w.WIN1P_WINP ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1_WIN := (@AFjm_w.WIN1_WIN ly regs0 n idx res mb Hidx).
Local Abbreviation WIN1P_WIN1 := (@AFjm_w.WIN1P_WIN1 ly regs0 n idx mb).
Local Abbreviation LGv_range := (@AFjm_w.LGv_range n Nrange).
Local Abbreviation BSLv_range := (@AFjm_w.BSLv_range ly regs0 n idx res mb Nrange Hidx).
Local Abbreviation WSKELP := (@AFjm_w.WSKELP).
Local Abbreviation WSKEL1P := (@AFjm_w.WSKEL1P).
Local Abbreviation WMAP := (@AFjm_w.WMAP).
Local Abbreviation WSKEL := (@AFjm_w.WSKEL).
Local Abbreviation WSKEL1 := (@AFjm_w.WSKEL1).
Local Abbreviation win_sub := (@AFjm_w.win_sub).
Local Abbreviation win_sub_sound := (@AFjm_w.win_sub_sound ly regs0 idx res mb Hidx Hres).
Local Abbreviation in_win := (@AFjm_w.in_win).
Local Abbreviation WSKELP_WINP := (@AFjm_w.WSKELP_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WSKEL1P_WIN1P := (@AFjm_w.WSKEL1P_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation WMAP_WINM := (@AFjm_w.WMAP_WINM _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL_WIN := (@AFjm_w.WSKEL_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WSKEL1_WIN1 := (@AFjm_w.WSKEL1_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_in := (@AFjm_w.windows_in ly regs0 idx res mb Hidx Hres).
Local Abbreviation windows_WINP := (@AFjm_w.windows_WINP _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN1P := (@AFjm_w.windows_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation windows_WIN := (@AFjm_w.windows_WIN _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1 := (@AFjm_w.windows_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation frame_WIN1P := (@AFjm_w.frame_WIN1P _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation frame_WIN1 := (@AFjm_w.frame_WIN1 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WINP_not_high := (@AFjm_w.WINP_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation WIN_not_high := (@AFjm_w.WIN_not_high _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52bac) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Local Abbreviation all_disjoint_of_forall := (@AFjm_w.all_disjoint_of_forall).
Local Abbreviation img_rw_writable := (@AFjm_w.img_rw_writable ly regs0 idx res mb Hidx).
Local Abbreviation kept_of_frame := (@AFjm_w.kept_of_frame W ly regs0 idx res mb Hidx).
Local Abbreviation SKEL_TAIL := (@AFjm_w.SKEL_TAIL).
Local Abbreviation blocks_facts := (@AFjm_w.blocks_facts _ ly LY IMG).
Local Abbreviation off_T := (@AFjm_w.off_T _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_C := (@AFjm_w.off_C _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_Q := (@AFjm_w.off_Q _ ly regs0 idx res LY IMG Hidx Hres).
Local Abbreviation off_NB := (@AFjm_w.off_NB _ ly LY IMG).
Local Abbreviation off_SB := (@AFjm_w.off_SB _ ly LY IMG).
Local Abbreviation off_shadow := (@AFjm_w.off_shadow ly regs0 idx res mb Hidx).
Ltac off_by tac :=
first [ apply off_img_high; tac | apply off_T; tac | apply off_C; tac | apply off_Q; tac | apply off_NB; tac | apply off_SB; tac
| apply map_off_img; tac | apply off_shadow; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; tac ].
Local Abbreviation DZONE := (@AFjm_w.DZONE ly).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Local Abbreviation DZONE_disj := (@AFjm_w.DZONE_disj _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation RFACTS := (@AFjm_w.RFACTS ly regs0).
Local Abbreviation zone_lit := (@AFjm_w.zone_lit _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_irw := (@AFjm_w.zone_irw _ ly regs0 LY IMG Hsp).
Local Abbreviation zone_T := (@AFjm_w.zone_T _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation zone_C := (@AFjm_w.zone_C _ ly regs0 idx res LY IMG Hsp Hidx Hres).
Local Abbreviation tail_ext_ok := (@AFjm_w.tail_ext_ok _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation RFACTS_map := (@AFjm_w.RFACTS_map _ ly regs0 n idx res mb LY IMG Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_ST := (@AFjm_w.at_ST _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretch := (@AFjm_w.memset_stretch _ _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation at_S := (@AFjm_w.at_S _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_N := (@AFjm_w.at_N _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_RETS := (@AFjm_w.at_RETS _ regs0 mem0).
Local Abbreviation pstable := (@AFjm_w.pstable).
Local Abbreviation stack_shaped := (@AFjm_w.stack_shaped).
Local Abbreviation window_present := (@AFjm_w.window_present ly regs0 idx res Hidx).
Local Abbreviation stack_present_of := (@AFjm_w.stack_present_of _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation mid_not_WIN1P := (@AFjm_w.mid_not_WIN1P _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1 := (@AFjm_w.mid_not_WIN1 _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation wins_ok := (@AFjm_w.wins_ok).
Local Abbreviation at_S_run_gen := (@AFjm_w.at_S_run_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_run_ecall_gen := (@AFjm_w.at_S_run_ecall_gen _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
Local Abbreviation at_S_runP := (@AFjm_w.at_S_runP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runM := (@AFjm_w.at_S_runM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallP := (@AFjm_w.at_S_run_ecallP _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_run_ecallM := (@AFjm_w.at_S_run_ecallM _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_pin := (@AFjm_w.at_S_pin _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_arm := (@AFjm_w.at_S_arm _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_forget := (@AFjm_w.at_S_forget _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_noconds := (@AFjm_w.at_S_noconds _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_weaken := (@AFjm_w.at_S_weaken _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_facts := (@AFjm_w.at_S_facts _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_strengthen := (@AFjm_w.at_S_strengthen _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_eq := (@AFjm_w.at_S_eq _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation at_S_open := (@AFjm_w.at_S_open _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation CSAVEDS := (@AFjm_w.CSAVEDS).
Local Abbreviation sv_denot_SOff0 := (@AFjm_w.sv_denot_SOff0).
Local Abbreviation at_S_ret := (@AFjm_w.at_S_ret _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Htp Hra Hsp Nrange Hidx Hres).
Local Abbreviation kept_of_frame2 := (@AFjm_w.kept_of_frame2 ly regs0 idx res Hidx).
Local Abbreviation at_N_cont := (@AFjm_w.at_N_cont _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Hidx).
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
Hypothesis Hj6 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa1c18 8 j6.
Hypothesis Hj7 : val_mem tfibsegs (mrestrict (w_H W) mem0) 0xa1c20 8 j7.
Hypothesis Hj8 : val_mem tfibsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qmeter S.
Local Abbreviation vis_present := (@AFjv_w.vis_present _ W ly regs0 mem0 idx res Hidx DPOST B S HARm).
Local Abbreviation in_thread_junk := (@AFjv_w.in_thread_junk ly B S).
Local Abbreviation in_sec_junk := (@AFjv_w.in_sec_junk ly B S).
Local Abbreviation in_as_junk := (@AFjv_w.in_as_junk ly B S).
Local Abbreviation junk_word := (@AFjv_w.junk_word _ W ly regs0 mem0 idx res LY IMG Hidx Hres DPOST B S HARm).
Local Abbreviation cell_sym := (@AFjv_w.cell_sym _ W ly mem0 B S TS HARm).
Local Abbreviation cell_lit := (@AFjv_w.cell_lit _ W ly mem0 B S TS HARm).
Local Abbreviation cell_state := (@AFjv_w.cell_state _ W ly mem0 B S HARm).
Local Abbreviation In_acells_sec := (@AFjv_w.In_acells_sec ly B S).
Local Abbreviation sec_vals := (@AFjv_w.sec_vals _ W ly mem0 idx res B S TS HARm Hidx_def Hres_def).
Local Abbreviation unwinding_val := (@AFjv_w.unwinding_val _ W ly mem0 B S HARm).
Local Abbreviation rw_writable := (@AFjv_w.rw_writable ly regs0 idx res Hidx DPOST S).
Local Abbreviation val_mem_mod8 := (@AFjv_w.val_mem_mod8 W ly regs0 mem0 idx res Hidx DPOST S).
Local Abbreviation chunk_lit := (@AFjv_w.chunk_lit W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_lit_at := (@AFjv_w.chunk_lit_at W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_atom := (@AFjv_w.chunk_atom W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx DPOST S).
Local Abbreviation SREG0_ok := (@AFjw_w.SREG0_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PAIRS_ok := (@AFjx_w.PAIRS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation FACTS_ok := (@AFjx_w.FACTS_ok _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation SEED_ok := (@AFjx_w.SEED_ok _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hsp Nrange Hidx Hres Hpres0 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation PBUF := (@AFjh_w.PBUF W ly regs0 ch).
Local Abbreviation PBUF_stableP := (@AFjh_w.PBUF_stableP _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableM := (@AFjh_w.PBUF_stableM _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation seg0 := (@AFjh_w.seg0 _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Htp Hra4096 Hsp Hch Nrange Hidx Hres Hpres0 mat0 U1 DPOST B S TS HTSD HARm Hidx_def Hres_def Hj0 Hj1 Hj2 Hj3 Hj4 Hj5 Hj9 Hj6 Hj7 Hj8 Hi1 Hi2 Hi3).
Local Abbreviation appregs := (@AFjn_w.appregs).
Local Abbreviation st_ok_appregs := (@AFjn_w.st_ok_appregs _).
Local Abbreviation at_S_app := (@AFjn_w.at_S_app _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation WIN1N := (@AFjn_w.WIN1N ly regs0 n).
Local Abbreviation WINPN := (@AFjn_w.WINPN ly regs0 n).
Local Abbreviation WSKEL1N := (@AFjn_w.WSKEL1N).
Local Abbreviation WIN1N_WINPN := (@AFjn_w.WIN1N_WINPN ly regs0 n idx res mb Hidx).
Local Abbreviation windows_WIN1N := (@AFjn_w.windows_WIN1N _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres).
Local Abbreviation mid_not_WIN1N := (@AFjn_w.mid_not_WIN1N _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_runN := (@AFjn_w.at_S_runN _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation PBUF_stableN := (@AFjn_w.PBUF_stableN _ W ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres).
Local Abbreviation at_S_val := (@AFjn_w.at_S_val _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation memset_stretchW := (@AFjn_w.memset_stretchW _ W ly regs0 mem0 n idx res Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation at_S_memset := (@AFjn_w.at_S_memset _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hsp Nrange Hidx Hres DPOST S).
Local Abbreviation WIN1T := (@AFjn_w.WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1T_WIN := (@AFjn_w.WIN1T_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1T := (@AFjn_w.windows_WIN1T _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation WIN1T_WIN1_aux := (@AFjn_w.WIN1T_WIN1_aux _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1T := (@AFjn_w.mid_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runT := (@AFjn_w.at_S_runT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallT := (@AFjn_w.at_S_run_ecallT _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PBUFW := (@AFjn_w.PBUFW ly regs0 ch).
Local Abbreviation PBUFW_stableT := (@AFjn_w.PBUFW_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation WIN1S := (@AFjo_w.WIN1S ly regs0 n idx mb).
Local Abbreviation WSKEL1S := (@AFjo_w.WSKEL1S).
Local Abbreviation WIN1S_WIN1T := (@AFjo_w.WIN1S_WIN1T ly regs0 n idx mb).
Local Abbreviation WIN1S_WIN := (@AFjo_w.WIN1S_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1S := (@AFjo_w.windows_WIN1S _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1S := (@AFjo_w.mid_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runS := (@AFjo_w.at_S_runS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallS := (@AFjo_w.at_S_run_ecallS _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation brun := (@AFjo_w.brun).
Local Abbreviation run_ok := (@AFjo_w.run_ok n mb).
Local Abbreviation PS := (@AFjo_w.PS ly regs0 n ch mb).
Local Abbreviation runs_not_WIN1S := (@AFjo_w.runs_not_WIN1S _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation runs_not_stack := (@AFjo_w.runs_not_stack _ ly regs0 n idx res mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PS_stable := (@AFjo_w.PS_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation cut1 := (@AFjo_w.cut1).
Local Abbreviation cut := (@AFjo_w.cut).
Local Abbreviation cut_sound := (@AFjo_w.cut_sound _ ly regs0 mem0 n idx res mb Nrange Hidx Hres Hmap DPOST S).
Local Abbreviation cut_ok := (@AFjo_w.cut_ok ly regs0 mem0 n idx res mb Hidx Hres DPOST S).
Local Abbreviation at_S_memsetS := (@AFjo_w.at_S_memsetS _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation skel_okb := (@AFjo_w.skel_okb).
Local Abbreviation skel_cases := (@AFjo_w.skel_cases idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation skel_apart := (@AFjo_w.skel_apart _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_u64 := (@AFjo_w.skel_u64 _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation memset_ext_of_skel := (@AFjo_w.memset_ext_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation memset_u64_of_skel := (@AFjo_w.memset_u64_of_skel _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap DPOST S Hidx_def Hres_def).
Local Abbreviation WIN1R := (@AFjo_w.WIN1R ly regs0 n mb).
Local Abbreviation WSKEL1R := (@AFjo_w.WSKEL1R).
Local Abbreviation WIN1R_WIN1S := (@AFjo_w.WIN1R_WIN1S ly regs0 n idx mb).
Local Abbreviation WIN1R_WIN := (@AFjo_w.WIN1R_WIN _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation windows_WIN1R := (@AFjo_w.windows_WIN1R _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Nrange Hidx Hres Hmap).
Local Abbreviation mid_not_WIN1R := (@AFjo_w.mid_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_runR := (@AFjo_w.at_S_runR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation at_S_run_ecallR := (@AFjo_w.at_S_run_ecallR _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap).
Local Abbreviation PSR := (@AFjo_w.PSR ly regs0 n ch mb).
Local Abbreviation rstable := (@AFjo_w.rstable ly regs0 n mb).
Local Abbreviation rstable_true := (@AFjo_w.rstable_true ly regs0 n mb).
Local Abbreviation PSR_stable := (@AFjo_w.PSR_stable _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP := (@AFjo_w.QSP ly idx).
Local Abbreviation QS_not_WIN1R := (@AFjo_w.QS_not_WIN1R _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation QSP_rstable := (@AFjo_w.QSP_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation at_S_memsetSR := (@AFjo_w.at_S_memsetSR _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation chunk_eqb := (@AFjo_w.chunk_eqb).
Local Abbreviation chunk_eqb_eq := (@AFjo_w.chunk_eqb_eq idx res Hidx Hres S Hidx_def Hres_def).
Local Abbreviation subregionb := (@AFjo_w.subregionb).
Local Abbreviation subregionb_sound := (@AFjo_w.subregionb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation submemb := (@AFjo_w.submemb).
Local Abbreviation submemb_sound := (@AFjo_w.submemb_sound ly regs0 mem0 idx res Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_submem := (@AFjo_w.at_S_submem _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres DPOST S Hidx_def Hres_def).
Local Abbreviation at_S_addreg := (@AFjo_w.at_S_addreg _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation PSR_runs := (@AFjk_w.PSR_runs _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation place_WIN := (@AFjk_w.place_WIN ly regs0 n idx mb).
Local Abbreviation SH0 := (@AFjk_w.SH0 n mb).
Local Abbreviation SH1 := (@AFjk_w.SH1 n mb).
Local Abbreviation SH2 := (@AFjk_w.SH2 n mb).
Local Abbreviation SH_ok := (@AFjk_w.SH_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segG1 := (@AFjk_w.segG1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QR := (@AFjp_w.QR ly res).
Local Abbreviation segT1 := (@AFjp_w.segT1 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation DX := (@AFjp_w.DX ly regs0).
Local Abbreviation PD := (@AFjp_w.PD ly mem0 DPOST).
Local Abbreviation PD_rstable := (@AFjp_w.PD_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PD_stableT := (@AFjp_w.PD_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PSR_stableS := (@AFjp_w.PSR_stableS _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation PD_stableS := (@AFjp_w.PD_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX := (@AFjp_w.PDX ly mem0 DPOST).
Local Abbreviation PDX_rstable := (@AFjp_w.PDX_rstable _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableT := (@AFjp_w.PDX_stableT _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation PDX_stableS := (@AFjp_w.PDX_stableS _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST).
Local Abbreviation dx_okb := (@AFjp_w.dx_okb).
Local Abbreviation skel_apart_DX := (@AFjp_w.skel_apart_DX _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation skel_apart_stk := (@AFjp_w.skel_apart_stk _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation at_S_depot := (@AFjp_w.at_S_depot _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH3 := (@AFjp_w.SH3 n mb).
Local Abbreviation SH4 := (@AFjp_w.SH4 n mb).
Local Abbreviation shadow_marks := (@AFjp_w.shadow_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH34_ok := (@AFjp_w.SH34_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segT2b := (@AFjp_w.segT2b _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segT2 := (@AFjp_w.segT2 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH5 := (@AFjq_w.SH5 n mb).
Local Abbreviation SH6 := (@AFjq_w.SH6 n mb).
Local Abbreviation user_marks := (@AFjq_w.user_marks _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation SH56_ok := (@AFjq_w.SH56_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segU1 := (@AFjq_w.segU1 _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation SH6_of_cut := (@AFjq_w.SH6_of_cut _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation segUe := (@AFjq_w.segUe _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation PT := (@AFjq_w.PT ly regs0 n ch mb).
Local Abbreviation run_okT := (@AFjq_w.run_okT n mb).
Local Abbreviation SH5o := (@AFjq_w.SH5o n mb).
Local Abbreviation SH6o := (@AFjq_w.SH6o n mb).
Local Abbreviation SH56o_ok := (@AFjq_w.SH56o_ok _ ly regs0 n idx res mb Nrange Hidx Hres Hmap).
Local Abbreviation PT_stableT := (@AFjq_w.PT_stableT _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation segUo := (@AFjq_w.segUo _ _ W ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hn Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Definition E0_at (mb0 : Z) : env := @AFjm_w.E0 ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb0.
Definition map_atom (k : nat) : bool := natin [aMAP; aEND; aSM; aUE; aPBS] k.
Lemma E0_at_other : forall mb0 k, (k < sHAV)%nat -> map_atom k = false -> ew (E0_at mb0) k = ew E0 k.
Proof.
clearP. intros mb0 k Hk Hm. unfold sHAV in Hk.
do 80 (destruct k as [|k]; [first [reflexivity | discriminate Hm] |]). exfalso. clear - Hk. zlia.
Qed.
Lemma ed_E0_at : forall mb0, ed (E0_at mb0) = ed E0.
Proof. clearP. intros; reflexivity. Qed.
Lemma st_ok_ecall_agree_on : forall P (E E' : env) ss ms,
st_ok_ecall tfibsegs E ss ms -> env_agree_on P E E' -> ss_atoms_in P ss = true -> st_ok_ecall tfibsegs E' ss ms.
Proof.
clearP. intros P E E' ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HA Hat.
unfold ss_atoms_in in Hat. apply andb_prop in Hat as [Hat Hrv]. apply andb_prop in Hat as [Hat HG]. apply andb_prop in Hat as [Hr Hm].
unfold st_ok_ecall. split; [exact H1|]. split; [exact H2|]. split.
{ rewrite H3. rewrite (sv_denot_agree_on P E E') by (try assumption; apply sr_get_atoms_in; exact Hr). reflexivity. }
split. { rewrite H4. destruct (ss_resv ss) as [a|]; cbn; [|reflexivity]. rewrite (sv_denot_agree_on P E E') by assumption. reflexivity. }
split; [exact H5|]. split; [exact H6|]. split; [eapply regs_ok_agree_on; eauto|]. split; [eapply mem_ok_agree_on; eauto | eapply facts_ok_agree_on; eauto].
Qed.
Definition Esw (E' : env) : env := env_merge map_atom E0 E'.
Lemma Esw_agree : forall mb0 (E' : env), env_agree sHAV (E0_at mb0) E' -> env_agree sHAV E0 (Esw E').
Proof.
clearP. intros mb0 E' [HA HD]. split.
- intros k Hk. unfold Esw. destruct (map_atom k) eqn:Hm.
+ rewrite (ew_merge_in _ _ _ _ Hm). reflexivity.
+ rewrite (ew_merge_out _ _ _ _ Hm), (HA k Hk). exact (E0_at_other mb0 k Hk Hm).
- unfold Esw. rewrite ed_merge, HD. apply ed_E0_at.
Qed.
Lemma Esw_on : forall E' : env, env_agree_on (fun k => negb (map_atom k)) E' (Esw E').
Proof. clearP. intros E' k Hk. unfold Esw. apply Bool.negb_true_iff in Hk. rewrite (ew_merge_out _ _ _ _ Hk). reflexivity. Qed.
Lemma at_S_facts_atoms : forall (Wx : world tfibsegs) md X P ss W' c' (ats : list (nat * afact)),
at_S Wx md X P ss W' c' -> f_conds (ss_facts ss) = [] -> f_alias (ss_facts ss) = [] ->
atoms_ok E0 ats -> forallb (fun p => Nat.ltb (fst p) sHAV) ats = true ->
at_S Wx md X P (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) (mkFacts ats [] [])) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' ats HR Hc Ha HOK Hlt. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|split; [exact I | exact I]]. cbn [f_atoms].
clear - HOK Hlt HE. destruct HE as [HA _]. induction ats as [|[k f] l IH]; [exact I|]. cbn [atoms_ok forallb fst] in HOK, Hlt |- *. apply andb_prop in Hlt as [Hk Hl]. destruct HOK as [Hf Hrest].
split; [|exact (IH Hrest Hl)]. unfold afact_ok in *. apply Nat.ltb_lt in Hk. rewrite (HA k Hk). exact Hf.
Qed.
Lemma atoms_ok_app : forall (E : env) l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. clearP. intros E l1 l2 H1 H2. induction l1 as [|[k f] l IH]; [exact H2|]. cbn in H1 |- *. destruct H1 as [Hf Hl]. split; [exact Hf | exact (IH Hl)]. Qed.
Lemma FS2_ok : atoms_ok E0 (f_atoms FS2).
Proof.
pose proof FACTS_ok as F1. unfold FS2, FS in *. cbn [f_atoms] in *. unfold FS2_atoms. apply atoms_ok_app; [exact F1|].
pose proof map_facts as (M1 & M2 & M3 & K4 & U5 & E6 & UE7 & E8 & UE9 & MT & MU & SM1 & SM2 & SM3 & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14). pose proof Nrange as NR. pose proof Hidx as HI.
pose proof BSLv_range as HB. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _).
pose proof shadow_marks as (_ & A2 & A3 & _ & A5 & A6 & _). pose proof user_marks as (B1 & _ & _ & B4 & _).
clear - F1 M1 M2 M3 K4 U5 E6 UE7 E8 UE9 MT MU SM1 SM2 SM3 PB Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 NR HI HB F9 F10 F11 A2 A3 A5 A6 B1 B4 MZ.
unfold MALLOC_MAX in *. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks in *. unfold TFIB_INST in HB |- *.
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; zlia. }
assert (M12 : mb mod 2 ^ 12 = 0) by (change (2 ^ 12) with 4096; exact M3).
assert (E3 : ENDv mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact E8). assert (UE3 : UEv mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact UE9).
assert (TL3 : TLv mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Z12). assert (RL3 : RLv mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Z14).
assert (N83 : N8D mod 2 ^ 3 = 0) by (change (2 ^ 3) with 8; exact Z5).
assert (QS3 : QSv mod 2 ^ 3 = 0).
{ unfold QSv. change (2 ^ 3) with 8. unfold page_aligned in F11. apply Z.mod_divide in F11 as [q Hq]; [|zlia]. try unfold Qb. rewrite Hq.
replace (q * 4096 + 8 * idx) with ((q * 512 + idx) * 8) by zlia. apply Z_mod_mult. }
assert (BS3 : BSLv mod 2 ^ 3 = 0).
(* Theorem Labs, 2026-10-29: 83476 -> 82752. C1: (83476+LGv)*8 is false; 661848+168 = 662016 = 82752*8. Found by a cross-check against port_core tag abfd17f8b3d2, class (c): the tag is right and applied-A was wrong. *)
{ unfold AFjm_w.BSLv. change (2 ^ 3) with 8. unfold TFIB_INST. replace (661848 + 168 + 8 * LGv) with ((82752 + LGv) * 8) by zlia. apply Z_mod_mult. }
assert (SM9 : SMv mod 2 ^ 9 = 0) by (change (2 ^ 9) with 512; exact SM3).
cbn [atoms_ok app fst snd]. unfold aMAP, aEND, aTL, aQS, aBSL, aSM, aUE, aRL, aN8DS, aPBS.
split; [apply (AF _ mb); [exact EaMAP | clear - M1 M2 Z8 MZ; zlia | clear - M1 M2 Z8 MZ; zlia | exact M12 | clear; zlia] |].
split; [apply (AF _ ENDv); [exact EaEND | clear - M1 M2 Z8 Z1 E6 U5 MT Z11 MZ; unfold Uv in *; zlia | clear - M1 M2 Z8 Z1 E6 U5 MT Z11 MZ; unfold Uv in *; zlia | exact E3 | clear; zlia] |].
split; [apply (AF _ TLv); [exact EaTL | clear - Z11 MZ; zlia | clear - Z11 MZ; zlia | exact TL3 | clear; zlia] |].
split; [apply (AF _ QSv); [exact EaQS | clear - F9 F10 HI MZ; unfold QSv; try unfold Qb in *; zlia | clear - F9 F10 HI MZ; unfold QSv; try unfold Qb in *; zlia | exact QS3 | clear; zlia] |].
split; [apply (AF _ BSLv); [exact EaBSL | clear - HB MZ; zlia | clear - HB MZ; zlia | exact BS3 | clear; zlia] |].
split; [apply (AF _ SMv); [exact EaSM | clear - SM1 SM2 Z8 MZ; zlia | clear - SM1 SM2 Z8 MZ; zlia | exact SM9 | clear; zlia] |].
split; [apply (AF _ UEv); [exact EaUE | clear - M1 M2 Z8 Z1 UE7 U5 MU Z13 MZ; unfold Uv in *; zlia | clear - M1 M2 Z8 Z1 UE7 U5 MU Z13 MZ; unfold Uv in *; zlia | exact UE3 | clear; zlia] |].
split; [apply (AF _ RLv); [exact EaRL | clear - Z13 MZ; zlia | clear - Z13 MZ; zlia | exact RL3 | clear; zlia] |].
split; [apply (AF _ N8D); [exact EaN8D | clear - Z4 NR MZ; zlia | clear - Z4 NR MZ; zlia | exact N83 | clear; zlia] |].
split; [apply (AF _ PBv); [exact EaPB | clear - A2 A3 A5 A6 B1 B4 SM1 SM2 MZ; zlia | clear - A2 A3 A5 A6 B1 B4 SM1 SM2 MZ; zlia | change (2 ^ 0) with 1; apply Z.mod_1_r | clear; zlia] | exact I].
Qed.
Lemma at_S_addreg_cfg : forall (Wx : world tfibsegs) md X P ss W' c' r,
at_S Wx md X P ss W' c' -> YP09.region_wf r = true ->
(forall (E' : env) (ms : machine_state) mat,
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) ->
env_agree sHAV E0 E' -> P (ms_mem ms) -> mem_ok tfibsegs E' (mrestrict (w_H Wx) (ms_mem ms)) (ss_mem ss) ->
region_ok tfibsegs E' (mrestrict (w_H Wx) (ms_mem ms)) r /\ (forall r2, In r2 (ss_mem ss) -> extent_disjoint E' r r2)) ->
at_S Wx md X P (addreg r ss) W' c'.
Proof.
clearP. intros Wx md X P ss W' c' r HR Hwf HOK. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
pose proof (st_ok_mem_ok tfibsegs E' ss _ HS) as HM. destruct (HOK E' ms mat eq_refl HE HPm HM) as [Hok Hx].
unfold addreg. apply st_ok_add_region; [exact HS | exact Hwf | exact Hok | apply all_disjoint_of_forall; exact Hx].
Qed.
Lemma S_N_apart : forall (E' : env), env_agree sHAV E0 E' ->
forall r a, In r (ss_mem S_N) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r ->
~ (mb <= a < mb + MSv) /\ 0 <= a < 2 ^ 64.
Proof.
intros E' [HE _] r a Hr Ha. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
lazymatch type of Hr with In _ ?l =>
let m3 := eval vm_compute in (firstn 3 l) in let tl3 := eval vm_compute in (skipn 3 l) in
assert (SPLIT : In r m3 \/ In (skel r) SKEL_TAIL)
by (change l with (m3 ++ tl3) in Hr; apply in_app_iff in Hr as [Hr|Hr]; [left; exact Hr | right];
apply (in_map skel) in Hr; replace (map skel tl3) with SKEL_TAIL in Hr by (vm_compute; reflexivity); exact Hr) end.
clear Hr. destruct SPLIT as [Hr|Hr].
- destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha; rewrite (HE 2%nat ltac:(unfold sHAV; zlia)), E2 in Ha;
clear - Ha MS S1 S3 T4 T7 U2; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia.
- pose proof (tail_ext_ok E' r HE Hr) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (RFACTS_map _ _ 0 0 (conj X1 (conj X2 (conj X3 (conj (or_introl (Z.le_refl 0)) (conj X5 X6)))))) as [AM _]. clear - Ha X2 X3 AM. zlia.
Qed.
Lemma S_N_nomap : ss_atoms_in (fun k => negb (map_atom k)) S_N = true.
Proof. clearP. vm_compute. reflexivity. Qed.
Lemma grant_cont : forall (mb0 : Z) (Wy : world tfibsegs) (md' : Model) (R : (word -> option byte) -> Prop) ms (E' : env),
env_agree sHAV (E0_at mb0) E' ->
st_ok_ecall tfibsegs E' S_N (restrict (w_H W) ms) ->
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
PBUF (ms_mem ms) ->
hsub (w_H Wy) (w_H W) ->
(forall a, mb <= a < mb + MSv -> w_H Wy (w64 a) = false) ->
(forall a, SMv <= a < SMv + MSv / 8 -> w_H Wy (w64 a) = false /\ ms_mem ms (w64 a) = Some (Z_to_bv 8 0)) ->
R (zfill (w64 mb) (w64 MSv) (ms_mem ms)) ->
at_S Wy md' WIN (PSR Wy SH0 R) S_P0 Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv (w64 mb)) (v_addi (Z_to_bv 64 (ss_pc S_N)) 4) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) (seg_rom tfibsegs)) md').
Proof.
intros mb0 Wy md' R ms E' HE' HS MEQ PRS HB Hsub HMV HSV HR.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, ASAN_CEIL in M1, M2, SM1, SM2. unfold MALLOC_MAX in Z8.
pose proof (Esw_agree mb0 E' HE') as HE. set (E'' := Esw E') in *.
assert (HS'' : st_ok_ecall tfibsegs E'' S_N (restrict (w_H W) ms)) by (exact (st_ok_ecall_agree_on _ E' E'' S_N _ HS (Esw_on E') S_N_nomap)).
assert (Umb : bv_unsigned (w64 mb) = mb) by (unfold w64; apply unsigned_lit_small; clear - M1 M2 Z8 MZ; zlia).
assert (Ums : bv_unsigned (w64 MSv) = MSv) by (unfold w64; apply unsigned_lit_small; clear - Z8 MZ; zlia).
assert (FRz : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> zfill (w64 mb) (w64 MSv) (ms_mem ms) x = ms_mem ms x).
{ intros x Hx. apply zfill_out. rewrite Umb, Ums. clear - Hx MZ. zlia. }
assert (ZIN : forall a, mb <= a < mb + MSv -> zfill (w64 mb) (w64 MSv) (ms_mem ms) (w64 a) = Some (Z_to_bv 8 0)).
{ intros a Ha. apply zfill_in. rewrite Umb, Ums. unfold w64. rewrite unsigned_lit_small by (clear - Ha M1 M2 Z8 MZ; zlia). exact Ha. }
pose proof (at_N_cont W Wy md' WINP (PSR Wy SH0 R) S_N (SOff aMAP 0) (w64 mb) (fun a => mb <= a < mb + MSv) (zfill (w64 mb) (w64 MSv) (ms_mem ms)) ms E''
HE HS'' eq_refl MEQ PRS Hsub) as C.
assert (HeMAP : sv_denot E'' (SOff aMAP 0) = w64 mb).
{ rewrite sv_denot_SOff0. subst E''. unfold Esw. rewrite (ew_merge_in map_atom E0 E' aMAP eq_refl). exact EaMAP. }
specialize (C HeMAP ltac:(vm_compute; reflexivity) FRz (S_N_apart E'' HE)).
assert (RWIN : forall r a, In r (ss_mem S_N) -> base_val E'' (YP09.r_base r) + YP09.r_wlo r <= a < base_val E'' (YP09.r_base r) + YP09.r_whi r -> ~ (mb <= a < mb + MSv) /\ 0 <= a < 2 ^ 64).
{ intros r a Hr Ha. destruct HS'' as (_ & _ & _ & _ & _ & _ & _ & (Hwf & _ & _) & _). pose proof (region_wf_facts r (regions_wf_In _ r Hwf Hr)) as (_ & WW & _). apply (S_N_apart E'' HE r a Hr). clear - Ha WW MZ. zlia. }
specialize (C RWIN). clear RWIN.
assert (STK : forall a, sp0 - ASTACK <= a < sp0 -> ~ (mb <= a < mb + MSv)).
{ intros a Ha Hm. destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). clear - Ha Hm MS S1 S3 T7 MZ. unfold ASTACK in *. try unfold sp0 in *. zlia. }
specialize (C STK).
assert (PF : PSR Wy SH0 R (zfill (w64 mb) (w64 MSv) (ms_mem ms))).
{ split; [|exact HR]. split; [|split; [|split]].
- intros i Hi. pose proof tr_length as LEN. pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
intros kk Hkk. pose proof (HB i Hi kk Hkk) as X.
lazymatch goal with |- mbyte _ _ ?A = _ =>
assert (RNG : sp0 - ASTACK <= A < sp0) by (clear - Hi Hkk LEN MZ; unfold IFRAME, ASTACK; zlia);
destruct (PRS _ RNG) as [HhW _];
assert (HhY : w_H Wy (Z_to_bv 64 A) = false) by (destruct (w_H Wy (Z_to_bv 64 A)) eqn:Ey; [rewrite (Hsub _ Ey) in HhW; discriminate HhW | reflexivity]);
unfold mbyte, mrestrict in X |- *; rewrite HhW in X; rewrite HhY; rewrite (FRz (Z_to_bv 64 A)); [exact X|];
rewrite unsigned_lit_small by (clear - RNG S1 S3 T4 T7 U2 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, IFRAME, ASTACK, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia);
apply STK; exact RNG
end.
- intros a Ha. split; [apply HMV; clear - Ha MZ; zlia|]. exists (Z_to_bv 8 0). unfold w64 in ZIN. apply ZIN. clear - Ha MZ; zlia.
- intros a Ha. destruct (HSV a Ha) as [Hy Hz]. split; [exact Hy|]. exists (Z_to_bv 8 0). unfold w64 in Hz, FRz |- *. rewrite FRz; [exact Hz|].
rewrite unsigned_lit_small by (clear - Ha SM1 SM2 MZ; zlia). clear - Ha M1 SM2 MZ. zlia.
- unfold SH0. apply Forall_cons; [|apply Forall_nil]. intros a Ha. cbn [fst snd] in Ha. destruct (HSV a Ha) as [_ Hz]. unfold w64 in Hz, FRz |- *. rewrite FRz; [exact Hz|].
rewrite unsigned_lit_small by (clear - Ha SM1 SM2 MZ; zlia). clear - Ha M1 SM2 MZ. zlia. }
specialize (C PF). clear PF.
apply (at_S_weaken Wy md' _ WIN _ (PSR Wy SH0 R)) in C; [| intros a [Ha|Ha]; [exact (WINP_WIN a Ha) | unfold WIN, WINM; right; right; right; right; left; exact Ha] | intros m Hm; exact Hm].
apply at_S_noconds in C.
apply (at_S_facts_atoms Wy md' WIN _ _ Wy _ (f_atoms FS2)) in C; [| reflexivity | reflexivity | exact FS2_ok | vm_compute; reflexivity].
apply (at_S_addreg_cfg Wy md' WIN _ _ Wy _ R_map) in C; [| reflexivity |].
2:{ intros E3 ms3 mat3 Hc HE3 [(HB3 & HM3 & HSH3 & HRs3) HQ3] HMok. pose proof (proj1 HE3) as HEn3.
assert (Hm3 : ms_mem ms3 = zfill (w64 mb) (w64 MSv) (ms_mem ms)) by (injection Hc as <- _; reflexivity).
rewrite Hm3 in *.
assert (BM : base_val E3 (Some aMAP) = mb) by (cbn [base_val]; unfold aMAP; rewrite (HEn3 45%nat ltac:(unfold sHAV; zlia)), EaMAP; exact Umb).
split.
- unfold region_ok, R_map. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BM.
split; [clear - M1 MZ; zlia|]. split; [clear - M2 Z8 MZ; zlia|]. split.
+ intros o Ho. apply apresent_writable_off; [off_by ltac:(clear - Ho M1 M2 Z8 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; zlia) |]. split; [apply HMV; clear - Ho Z8 MZ; zlia|].
exists (Z_to_bv 8 0). unfold w64 in ZIN. apply ZIN. clear - Ho Z8 MZ; zlia.
+ apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia |].
intros kk Hkk. destruct kk as [|kk]; [|cbn in Hkk; zlia]. unfold mbyte, mrestrict. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold w64 in HMV, ZIN |- *. rewrite (HMV (mb + 6129)) by (clear - Z8 MZ; zlia). rewrite (ZIN (mb + 6129)) by (clear - Z8 MZ; zlia). reflexivity.
- intros r2 Hr2. unfold extent_disjoint, R_map. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite !BM.
pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
destruct Hmap_apart as (_ & _ & _ & _ & _ & _ & MS). unfold zdisjoint in MS. cbn [fst snd] in MS.
lazymatch type of Hr2 with In _ ?l =>
let m3 := eval vm_compute in (firstn 3 l) in let tl3 := eval vm_compute in (skipn 3 l) in
assert (SPLIT : In r2 m3 \/ In (skel r2) SKEL_TAIL)
by (change l with (m3 ++ tl3) in Hr2; apply in_app_iff in Hr2 as [Hr2|Hr2]; [left; exact Hr2 | right];
apply (in_map skel) in Hr2; replace (map skel tl3) with SKEL_TAIL in Hr2 by (vm_compute; reflexivity); exact Hr2) end.
clear Hr2. destruct SPLIT as [Hr|Hr].
+ destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite (HEn3 2%nat ltac:(unfold sHAV; zlia)), E2;
clear - MS S1 S3 T4 T7 U2 Z8 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, ASTACK, IFRAME, kHighMemBeg, kHighMemEnd in *; try unfold sp0 in *; zlia.
+ pose proof (tail_ext_ok E3 r2 HEn3 Hr) as (X1 & X2 & X3 & X4 & X5 & X6).
pose proof (RFACTS_map _ _ 0 0 (conj X1 (conj X2 (conj X3 (conj (or_introl (Z.le_refl 0)) (conj X5 X6)))))) as [AM _]. clear - AM Z8 MZ. zlia. }
lazymatch type of C with at_S _ _ _ _ ?ss2 _ _ => replace ss2 with S_P0 in C by (vm_compute; reflexivity) end.
exact C.
Qed.
End g.
End d.
