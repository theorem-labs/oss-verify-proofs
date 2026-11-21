(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFjz.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFjz.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AB1h_w AFjm_w AFia_w AFib_w AFid_w AFie_w AFif_w AFig_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YFen.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFjv_w AFjw_w AFjx_w AFjh_w AFjn_w AFjo_w AFjk_w AFjl_w AFjp_w AFjq_w AFjs_w AFju_w AFjt_w AFjy_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0b_w.
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
Section f.
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
Local Abbreviation RX_stableS := (@AFjl_w.RX_stableS ly regs0 n idx mb).
Local Abbreviation rstable_and := (@AFjl_w.rstable_and ly regs0 n mb).
Local Abbreviation pstable_and := (@AFjl_w.pstable_and).
Local Abbreviation PSR_stableS' := (@AFjl_w.PSR_stableS' _ ly regs0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation pairwise_disjoint_map := (@AFjl_w.pairwise_disjoint_map).
Local Abbreviation at_S_setchunks := (@AFjl_w.at_S_setchunks _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation chunk_ok_CVal_eqv := (@AFjl_w.chunk_ok_CVal_eqv).
Local Abbreviation RES2T_ne := (@AFjl_w.RES2T_ne ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation RES2T_eq := (@AFjl_w.RES2T_eq ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb Hidx Hres).
Local Abbreviation sv_denot_eq_of_U := (@AFjl_w.sv_denot_eq_of_U ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb).
Local Abbreviation skel_apart_QS := (@AFjl_w.skel_apart_QS _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation QSPX := (@AFjl_w.QSPX ly idx).
Local Abbreviation segNE := (@AFjl_w.segNE _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segEQa := (@AFjl_w.segEQa _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart).
Local Abbreviation zev_SAlu := (@AFjl_w.zev_SAlu).
Local Abbreviation zev_SLit := (@AFjl_w.zev_SLit).
Local Abbreviation zev_SOff := (@AFjl_w.zev_SOff).
Local Abbreviation segJ2 := (@AFjl_w.segJ2 _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation segJ := (@AFjl_w.segJ _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
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
Local Abbreviation SHLO := (@AFjs_w.SHLO).
Local Abbreviation SHHI := (@AFjs_w.SHHI n).
Local Abbreviation SH_hull := (@AFjs_w.SH_hull ly regs0 n res Nrange S).
Local Abbreviation lit_m1 := (@AFjs_w.lit_m1).
Local Abbreviation lit_enomem := (@AFjs_w.lit_enomem).
Local Abbreviation nores34 := (@AFjs_w.nores34).
Local Abbreviation core34 := (@AFjs_w.core34).
Local Abbreviation pru_MS := (@AFjs_w.pru_MS ly regs0 n res Nrange S).
Local Abbreviation grant_anon_shape := (@AFjs_w.grant_anon_shape).
Local Abbreviation Hcut_out := (@AFjs_w.Hcut_out).
Local Abbreviation slackS := (@AFjs_w.slackS _ W ly mem0 md0 B S HARm HQT).
Local Abbreviation S_N_facts := (@AFjs_w.S_N_facts).
Local Abbreviation S_N_ext64 := (@AFjs_w.S_N_ext64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation S_N_win64 := (@AFjs_w.S_N_win64 _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres S).
Local Abbreviation nodeS := (@AFjs_w.nodeS _ _ W ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres B S HARm HQT).
Local Abbreviation CZI := (@AFju_w.CZI).
Local Abbreviation CZ := (@AFju_w.CZ ly).
Local Abbreviation abs_cell_okS := (@AFju_w.abs_cell_okS).
Local Abbreviation abs_cells_okS := (@AFju_w.abs_cells_okS).
Local Abbreviation MPAD := (@AFju_w.MPAD).
Local Abbreviation padb := (@AFju_w.padb).
Local Abbreviation const_cells_CZ := (@AFju_w.const_cells_CZ ly regs0 n idx res mb Nrange Hidx B TS HTSD).
Local Abbreviation CZ_untouched := (@AFju_w.CZ_untouched _ ly regs0 mem0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S).
Local Abbreviation cell_holds_agree := (@AFju_w.cell_holds_agree ly regs0 mem0 idx res Hidx Hres DPOST B S).
Local Abbreviation aview_agreeW := (@AFju_w.aview_agreeW W).
Local Abbreviation rd_ext_Wy := (@AFju_w.rd_ext_Wy W).
Local Abbreviation depot_ids_bound := (@AFju_w.depot_ids_bound ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_agree := (@AFju_w.depot_mem_ok_agree ly regs0 mem0 idx res mb Hidx Hres DPOST B S TS).
Local Abbreviation depot_mem_ok_ext := (@AFju_w.depot_mem_ok_ext ly B).
Local Abbreviation depot_at0 := (@AFju_w.depot_at0 _ W ly regs0 mem0 n idx res mb Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S HARm).
Local Abbreviation DPOSTS := (@AFju_w.DPOSTS ly regs0 ch B S).
Local Abbreviation D1W_ok := (@AFju_w.D1W_ok _ _ W ly regs0 mem0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hgp).
Local Abbreviation S_VG := (@AFjt_w.S_VG).
Local Abbreviation TQ := (@AFjt_w.TQ).
Local Abbreviation S_V_facts := (@AFjt_w.S_V_facts).
Local Abbreviation ZQF := (@AFjt_w.ZQF ly res).
Local Abbreviation ZQ := (@AFjt_w.ZQ ly idx res).
Local Abbreviation QR_facts := (@AFjt_w.QR_facts _ ly regs0 idx res mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation ZQ_of_ZQF := (@AFjt_w.ZQ_of_ZQF ly idx res).
Local Abbreviation QR_not_WIN1T := (@AFjt_w.QR_not_WIN1T _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableT := (@AFjt_w.ZQ_stableT _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_rstable := (@AFjt_w.ZQ_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation ZQ_stableD := (@AFjt_w.ZQ_stableD _ ly regs0 idx res mb LY IMG Hsp Hidx Hres S Hidx_def).
Local Abbreviation skel_apart_Q := (@AFjt_w.skel_apart_Q _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def Hres_def).
Local Abbreviation TQ_val := (@AFjt_w.TQ_val _ ly regs0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hidx Hres S Hidx_def).
Local Abbreviation nores50 := (@AFjt_w.nores50).
Local Abbreviation core50 := (@AFjt_w.core50).
Local Abbreviation pru17 := (@AFjt_w.pru17).
Local Abbreviation grant_piece_shape := (@AFjt_w.grant_piece_shape).
Local Abbreviation nodeV := (@AFjt_w.nodeV _ _ ly regs0 mem0 md0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation RZF := (@AFjt_w.RZF ly res).
Local Abbreviation RZ := (@AFjt_w.RZ ly idx res).
Local Abbreviation ZQF_rstable := (@AFjt_w.ZQF_rstable _ ly regs0 n idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart S Hidx_def).
Local Abbreviation segV := (@AFjt_w.segV _ _ ly regs0 mem0 n ch idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST S Hidx_def Hres_def).
Local Abbreviation lyF := (@AFjy_w.lyF ly mb S).
Local Abbreviation SFS := (@AFjy_w.SFS ly regs0 n ch S).
Local Abbreviation KSc := (@AFjy_w.KSc n S).
Local Abbreviation lyF_le := (@AFjy_w.lyF_le ly mb S).
Local Abbreviation lyF_sec := (@AFjy_w.lyF_sec ly mb S).
Local Abbreviation lyF_eqs := (@AFjy_w.lyF_eqs ly mb S).
Local Abbreviation lyF_ok := (@AFjy_w.lyF_ok _ ly mb LY S).
Local Abbreviation sizes_model := (@AFjy_w.sizes_model ly regs0 n res Nrange S).
Local Abbreviation val_mem_cell := (@AFjy_w.val_mem_cell ly regs0 res B S).
Local Abbreviation le_byte_1_0 := (@AFjy_w.le_byte_1_0 ly regs0 res S).
Local Abbreviation find_chunk_at_app1 := (@AFjy_w.find_chunk_at_app1 B).
Local Abbreviation find_chunk_at_app2 := (@AFjy_w.find_chunk_at_app2 B).
Local Abbreviation In_combine_seq_app := (@AFjy_w.In_combine_seq_app).
Local Abbreviation combine_seq_last := (@AFjy_w.combine_seq_last ly regs0 res S).
Local Abbreviation in_combine_seq := (@AFjy_w.in_combine_seq ly regs0 res S).
Local Abbreviation combine_seq_in := (@AFjy_w.combine_seq_in ly regs0 res S).
Local Abbreviation index_of_app_old := (@AFjy_w.index_of_app_old).
Local Abbreviation index_ofZ_app_old := (@AFjy_w.index_ofZ_app_old).
Local Abbreviation index_of_app_new := (@AFjy_w.index_of_app_new ly regs0 res S).
Local Abbreviation index_ofZ_app_new := (@AFjy_w.index_ofZ_app_new ly regs0 res S).
Local Abbreviation fin_facts := (@AFjy_w.fin_facts ly regs0 mem0 n ch idx res mb B S).
Local Abbreviation wz_facts := (@AFjy_w.wz_facts _ W ly regs0 n ch res mb S).
Local Abbreviation S_AR_final := (@AFjy_w.S_AR_final _ W ly regs0 mem0 md0 n ch idx res mb LY IMG Hsp Nrange Hidx Hres Hmap Hmap_apart DPOST B S TS HTSD HARm Hidx_def Hres_def).
Local Abbreviation SF_parts := (@AFjy_w.SF_parts ly regs0 n ch res S Hres_def).
Local Abbreviation rS_not_in_arr := (@AFjy_w.rS_not_in_arr _ W ly regs0 mem0 n res mb B S HARm).
Local Abbreviation len_arr := (@AFjy_w.len_arr idx S Hidx_def).
Local Abbreviation ck_base_new := (@AFjy_w.ck_base_new ly regs0 n res mb Nrange B S).
Local Abbreviation SEF := (@AFjy_w.SEF _ W ly regs0 mem0 n ch res mb Nrange B S HARm Hres_def).
Local Abbreviation staticF := (@AFjy_w.staticF ly mb S).
Local Abbreviation placed_finalG := (@AFjy_w.placed_finalG _ W ly regs0 mem0 md0 n ch idx res mb Nrange Hidx Hres Hmap B S HARm Hres_def).
Local Abbreviation sec_live_final := (@AFjy_w.sec_live_final ly regs0 n ch res mb Nrange S Hres_def).
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition FQ (Wz : world tfibsegs) (grow : bool) (m : word -> option byte) : Prop :=
let mr := mrestrict (w_H Wz) m in
val_mem tfibsegs mr QSv 8 mb /\ val_mem tfibsegs mr mb 8 mb /\ val_mem tfibsegs mr (mb + 8) 8 MSv /\ val_mem tfibsegs mr (mb + 16) 8 NDv /\ val_mem tfibsegs mr (mb + 24) 8 idx /\
val_mem tfibsegs mr Kv 8 0xCC6E96B9CC6E96B9 /\ val_mem tfibsegs mr (Kv + 8) 8 (Uv - 16) /\ val_mem tfibsegs mr (Uv - 16) 1 2 /\ val_mem tfibsegs mr (Uv - 15) 1 17 /\
val_mem tfibsegs mr (Uv - 14) 2 0 /\ val_mem tfibsegs mr (Uv - 12) 4 n /\ val_mem tfibsegs mr (T + t_unwinding) 1 0 /\
val_mem tfibsegs mr (TFIB_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res) /\ val_mem tfibsegs mr (TFIB_INST + o_sec_n) 8 (idx + 1) /\
val_mem tfibsegs mr (TFIB_INST + o_sec_mutex) 1 0 /\ val_mem tfibsegs mr (TFIB_INST + o_sec_mutex + 1) 1 0 /\ val_mem tfibsegs mr (TFIB_INST + o_sec_mutex + 2) 2 0 /\
(forall a, WINT a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + 6144) -> apresent (w_H Wz) m a) /\
(forall a, WINI a -> aview tfibsegs (w_H Wz) m a <> None).
Section g.
Variables (Wz : world tfibsegs) (mdl : Model) (X : Z -> Prop) (RX : (word -> option byte) -> Prop) (grow : bool) (z : Z).
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis HXsub : forall a, X a -> WIN a \/ (grow = true /\ QR a) \/ DX a.
Hypothesis HRXQ : grow = true -> forall m, RX m -> ZQ Wz m.
Hypothesis HDPOST : forall zz m, DPOST zz m ->
aok S (KDepot tr) zz /\ depot_mem_ok B ly (depot_after zz tr S) (aview tfibsegs (w_H Wz) m) /\ Forall (cell_holds B ly (aview tfibsegs (w_H Wz) m)) (as_const B ly).
Lemma srl32_n : Z.shiftr n 32 = 0.
Proof. clearP. pose proof Nrange as NR. unfold MALLOC_MAX in NR. rewrite Z.shiftr_div_pow2 by zlia. apply Z.div_small. zlia. Qed.
Lemma FQ_e : forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Ue_RET (restrict (w_H Wz) ms) -> FQ Wz grow (ms_mem ms).
Proof.
intros E' ms HE HS. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; apply unsigned_lit_small; zlia).
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; try unfold T; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; unfold TFIB_INST in *; zlia).
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
split. { memv HS 52%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | | destruct grow; unfold kPtrArrayEntriesPerCommit; zlia].
change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(vm_compute; reflexivity)).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_small. zlia. }
split. { memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 56%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
split. { memv HS 56%nat 1%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
split. { memv HS 56%nat 2%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
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
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB MZ; unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia).
apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (TFIB_INST + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (TFIB_INST + 128)) as [A2|A2]].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 52%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_reserved in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_sorted in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_stats in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 62%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_mutex in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; zlia]. }
Qed.
Lemma FQ_o : n mod 8 <> 0 -> forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfibsegs E' Uo_RET (restrict (w_H Wz) ms) ->
FQ Wz grow (ms_mem ms) /\ val_mem tfibsegs (mrestrict (w_H Wz) (ms_mem ms)) PBv 1 (n mod 8) /\ apresent (w_H Wz) (ms_mem ms) PBv.
Proof.
intros H8 E' ms HE HS. pose proof (proj1 HE) as HEn.
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof Nrange as NR. pose proof BSLv_range as HB.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, kThreadObjSize in *.
assert (UQS : bv_unsigned (ew E' 52) = QSv) by (rewrite (HEn 52%nat ltac:(unfold sHAV; zlia)), EaQS; unfold w64; apply unsigned_lit_small; unfold QSv; try unfold Qb; zlia).
assert (UMAP : bv_unsigned (ew E' 45) = mb) by (rewrite (HEn 45%nat ltac:(unfold sHAV; zlia)), EaMAP; unfold w64; apply unsigned_lit_small; zlia).
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; try unfold T; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; unfold TFIB_INST in *; zlia).
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
split. { memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | | destruct grow; unfold kPtrArrayEntriesPerCommit; zlia].
change (SAlu ALU_ADD (SOff 40 0) (SAlu ALU_SLL (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 41 0) (SOff 40 0)) (SLit 1)) (SLit 14))) with RES2T.
rewrite (sv_denot_agree sHAV E0 E' RES2T HE ltac:(vm_compute; reflexivity)).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E0 RES2T)). f_equal. change (bv_unsigned (sv_denot E0 RES2T)) with (U E0 RES2T).
destruct grow.
- rewrite (RES2T_eq (proj1 Hgrow eq_refl)). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. apply zcanon_small. unfold kPtrArrayEntriesPerCommit. zlia.
- assert (NE : idx <> res) by (intros E; pose proof (proj2 Hgrow E) as XX; discriminate XX).
rewrite (RES2T_ne NE). rewrite U_SOff. unfold aRES. rewrite EaRES. unfold w64. rewrite unsigned_lit_small by zlia. rewrite Z.add_0_r. apply zcanon_small. zlia. }
split. { memv HS 54%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | cbn [sv_denot]; rewrite (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; unfold w64; rewrite ?Zbv_add_unsigned; first [reflexivity | f_equal; zlia] | zlia]. }
split. { memv HS 57%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
split. { memv HS 57%nat 1%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
split. { memv HS 57%nat 2%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]. }
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
{ intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB MZ; unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia).
apply (writable_visible (w_H Wz) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- destruct (Z_lt_le_dec a (TFIB_INST + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (TFIB_INST + 128)) as [A2|A2]].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_reserved in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST in *; zlia].
+ eapply (st_ok_window_writable (w_H Wz) E' _ _ 55%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_sorted in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 56%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_stats in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 63%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 57%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_mutex in *; zlia].
- eapply (st_ok_window_writable (w_H Wz) E' _ _ 58%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; zlia]. }
Qed.
Local Ltac run_byte HR x :=
rewrite <- (Z_to_bv_bv_unsigned 64 x); apply HR; cbn [fst snd].
Lemma fin_pack : forall (odd : bool) regs' mem' memD,
(odd = true <-> n mod 8 <> 0) ->
getr regs' 10 = sv_denot E0 (SOff aMAP 6144) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) ->
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wz) mem' a) ->
(forall a, mb + 6144 <= a < mb + MSv -> apresent (w_H Wz) mem' a) ->
(forall a, SMv <= a < SMv + MSv / 8 -> (odd = true -> a <> PBv) -> apresent (w_H Wz) mem' a) ->
Forall (brun mem') (if odd then SH6o else SH6) ->
DPOST z memD -> (forall a, DZONE a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a) -> (forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) ->
RX mem' -> FQ Wz grow mem' ->
(odd = true -> val_mem tfibsegs (mrestrict (w_H Wz) mem') PBv 1 (n mod 8) /\ apresent (w_H Wz) mem' PBv) ->
fin_facts grow z Wz regs' mem' memD.
Proof.
intros odd regs' mem' memD Hodd R10 RCS MEQ PRS HM HSH HRUN DP PRD EQD HRX FQm HPB.
destruct FQm as (Qslot & Qh0 & Qh8 & Qh16 & Qh24 & Qmag & Qbk & Qst & Qb1 & Qb2 & Qn & Qunw & Qres & Qnch & Qmtx & Qp1 & Qp2 & QPR & QVISW).
destruct (HDPOST z memD DP) as (AOK & DEPD & CSTD).
assert (RUNS : brun mem' (Uv, Uv + 4096, 190) /\ brun mem' (SMv + 768, SMv + 768 + N8D / 8, 0) /\ brun mem' (SHBv + UEv / 8, SMv + MSv / 8, 250) /\
brun mem' (SMv + 512, SMv + 768, 250) /\ brun mem' (SMv, SMv + 512, 250)).
{ destruct odd; unfold SH6o, SH5o, SH6, SH5 in HRUN;
apply Forall_cons_iff in HRUN as [R0 HRUN]; apply Forall_cons_iff in HRUN as [R1 HRUN]; apply Forall_cons_iff in HRUN as [R2 HRUN];
apply Forall_cons_iff in HRUN as [R3 HRUN]; apply Forall_cons_iff in HRUN as [R4 _]; exact (conj R0 (conj R1 (conj R2 (conj R3 R4)))). }
destruct RUNS as (Rfill & Rzs & Rrt & Rhd & Rpg).
constructor.
- exact AOK.
- exact DEPD.
- exact CSTD.
- exact PRD.
- exact EQD.
- intros x N1 N2 N3. apply MEQ. intros HXx. destruct (HXsub _ HXx) as [Hw|[Hw|Hw]]; [exact (N1 Hw) | exact (N2 Hw) | exact (N3 Hw)].
- exact PRS.
- intros a Ha. destruct (Z_lt_le_dec a (mb + 6144)) as [Hl|Hl]; [apply QPR; right; right; zlia | apply HM; zlia].
- intros a Ha. destruct odd.
+ destruct (Z.eq_dec a PBv) as [->|Hne]; [exact (proj2 (HPB eq_refl)) | apply HSH; [exact Ha | intros _; exact Hne]].
+ apply HSH; [exact Ha | intros E; discriminate E].
- intros Hg a Hqa. destruct (zr_dec QSv (QSv + 8) a) as [Hs|Hs]; [apply QPR; right; left; exact Hs|].
destruct (HRXQ Hg _ HRX (proj1 Hgrow Hg) a Hqa Hs) as [Hh Hm]. split; [exact Hh | eexists; exact Hm].
- intros a [Hw|Hs]; apply QPR; [left; exact Hw | right; left; exact Hs].
- exact QVISW.
- rewrite R10. cbn [sv_denot]. unfold aMAP. rewrite EaMAP. unfold w64, Uv. rewrite Zbv_add_unsigned; first [reflexivity | f_equal; zlia].
- exact RCS.
- intros x [Hx|Hx].
+ destruct (Z_lt_le_dec (bv_unsigned x) (SMv + 512)) as [Hl|Hl]; [run_byte Rpg x; zlia | run_byte Rhd x; zlia].
+ run_byte Rrt x; exact Hx.
- intros x Hx. run_byte Rzs x; exact Hx.
- intros H8. exact (proj1 (HPB (proj2 Hodd H8))).
- exact Qunw.
- exact Qres.
- exact Qnch.
- exact Qmtx.
- intros k Hk. unfold aview.
assert (K : k = 1 \/ k = 2 \/ k = 3) by zlia. destruct K as [->|[->| ->]].
+ pose proof (Qp1 0%nat ltac:(zlia)) as Xb. rewrite Z.add_0_r in Xb. rewrite Xb. reflexivity.
+ pose proof (Qp2 0%nat ltac:(zlia)) as Xb. rewrite Z.add_0_r in Xb. replace (TFIB_INST + o_sec_mutex + 2) with (TFIB_INST + o_sec_mutex + 2) by zlia. rewrite Xb. reflexivity.
+ pose proof (Qp2 1%nat ltac:(zlia)) as Xb. replace (TFIB_INST + o_sec_mutex + 3) with (TFIB_INST + o_sec_mutex + 2 + Z.of_nat 1) by zlia. rewrite Xb. reflexivity.
- exact Qslot.
- exact Qh0.
- exact Qh8.
- exact Qh16.
- exact Qh24.
- exact Qmag.
- exact Qbk.
- exact Qst.
- exact Qb1.
- exact Qb2.
- exact Qn.
- intros x Hx. run_byte Rfill x; exact Hx.
Qed.
Definition fin_post (W2 : world tfibsegs) (c2 : config) : Prop :=
W2 = Wz /\ exists regs' mem' mat memD,
c2 = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdl) mat mdl) /\ fin_facts grow z Wz regs' mem' memD.
Lemma finE : n mod 8 = 0 -> forall W' c', at_S Wz mdl X (PSR Wz SH6 (PDX Wz RX z)) Ue_RET W' c' -> SRr tfibsegs W' c' fin_post.
Proof.
intros H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (FQ Wz grow) Ue_RET) in HR; [| intros E' ms HE HS; exact (FQ_e E' ms HE HS)].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Ue_RET _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ & PRS & (((HB & HM & HSH & HRUN) & ((memD & DP & PRD & EQD) & HRX)) & FQm)).
split; [reflexivity|]. exists regs', mem', mat, memD. split; [reflexivity|].
apply (fin_pack false); try assumption.
- split; [intros E; discriminate E | intros H; exfalso; exact (H H8)].
- intros a Ha _. exact (HSH a Ha).
- intros E; discriminate E.
Qed.
Lemma finO : n mod 8 <> 0 -> forall W' c', at_S Wz mdl X (PT Wz SH6o (PDX Wz RX z)) Uo_RET W' c' -> SRr tfibsegs W' c' fin_post.
Proof.
intros H8 W' c' HR.
apply (at_S_facts Wz mdl X _ (fun m => FQ Wz grow m /\ val_mem tfibsegs (mrestrict (w_H Wz) m) PBv 1 (n mod 8) /\ apresent (w_H Wz) m PBv) Uo_RET) in HR;
[| intros E' ms HE HS; exact (FQ_o H8 E' ms HE HS)].
eapply SRr_mono; [eapply (at_S_ret Wz mdl X _ Uo_RET _ _ (SOff aMAP 6144) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | repeat constructor] |].
intros W2 c2 _ (-> & regs' & mem' & mat & -> & R10 & RCS & MEQ & PRS & ((HB & HM & HSH & HRUN & ((memD & DP & PRD & EQD) & HRX)) & (FQm & QPB & QPBp))).
split; [reflexivity|]. exists regs', mem', mat, memD. split; [reflexivity|].
apply (fin_pack true); try assumption.
- split; [intros _; exact H8 | reflexivity].
- intros a Ha Hne. exact (HSH a Ha (Hne eq_refl)).
- intros _. exact (conj QPB QPBp).
Qed.
End g.
Lemma OWN_T : forall a, WINT a -> aowned B ly S a.
Proof.
clearP. intros a Hw. apply (own_core B ly S rd0 (ly_T ly, kThreadObjSize) a HARm); [unfold core_extents; cbn; tauto|].
cbn [fst snd]. unfold WINT, t_unwinding, kThreadObjSize in *. unfold T in Hw. clear - Hw. zlia.
Qed.
Lemma OWN_I : forall a, WINI a -> aowned B ly S a.
Proof.
clearP. intros a Hw. pose proof BSLv_range as HB. apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa1958, 0xa4808 - 0xa1958). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd].
unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. clear - Hw HB. zlia.
Qed.
Lemma OWN_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> aowned B ly S a.
Proof. clearP. intros a Ha. apply (own_core B ly S rd0 (ly_Q ly, kPtrArrayResv) a HARm); [unfold core_extents; cbn; tauto | cbn [fst snd]; unfold Qb in Ha; exact Ha]. Qed.
Lemma OWN_D : forall a, DZONE a -> aowned B ly S a.
Proof.
clearP. intros a Hd. unfold DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- apply (own_static B ly S rd0 a HARm). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa4810, 0x5c7610 - 0xa4810). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd]. clear - Hd. zlia.
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
unfold ck_user in Hr. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (AFib_w.padd_lt S _ _ (AFib_w.chunk_lt S _ _ _ _ WF k Hk))) in Hr.
fold (ck_user k) in Hr. pose proof (chunk_facts B ly S rd0 k HARm Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
destruct (extent_zone B ly S rd0 k HARm Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
-- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - Ha Hr X1 X2 MP3 G8 G5 MZ. zlia.
-- pose proof (proj1 (Forall_forall _ _) GAP (m, len) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as D. unfold zdisjoint in D. cbn [fst snd] in D.
clear - Ha Hr X1 X2 D G8 G5 MZ. unfold kPage in *. zlia.
*
apply Hnu. unfold ck_user in Hr. cbn [YG00.ck_beg KSc AFib_w.KS padd sptr_addr sptr_exp aeval] in Hr.
change (YG00.ck_rz (AFib_w.KS S n)) with (ck_rz KSc) in Hr. rewrite KR, KN, lyF_sec in Hr. unfold Uv. unfold kPage in Hr. clear - Hr MZ. zlia.
+
unfold frames in Hcp, Rfr. rewrite Rfr in Hcp. destruct cp as [cid pos]. cbn [fst snd] in Hr.
pose proof (frame_facts B ly S rd0 cid pos HARm Hcp) as (C1 & C2 & F1 & F2 & FA & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(zlia) ltac:(zlia)).
pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). unfold frame_addr, in_zr in Hr. rewrite E6 in Hr. cbn [fst snd] in Hr.
pose proof (proj1 (Forall_forall _ _) GAP (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto)) as D.
unfold zdisjoint in D. cbn [fst snd] in D.
destruct Hr as [Hr|Hr].
* clear - Ha Hr D P1 P2 C1 H MZ. unfold kFakeFramesOff in *. zlia.
* pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 P1 H MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kFakeFramesOff in *; zlia) ltac:(clear - P4 MZ; zlia) ltac:(clear - F1 P2 MZ; ceil; unfold zone3, TFIB_IMG_LO, in_app, ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg, kFakeStackSize in *; zlia)) as SBel.
pose proof (Z.div_pos (ly_F ly + fs_frame_off cid pos) 8 ltac:(clear - F1 P1 H MZ; unfold in_app, kFakeFramesOff in *; zlia) ltac:(zlia)) as SB0.
clear - Ha Hr SBel SB0 M1 MZ. unfold shadow_addr, SHADOW_OFF, zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. zlia.
Qed.
Section h.
Variables (grow : bool) (z : Z) (Wz : world tfibsegs) (mdl : Model).
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis LEz : wle W Wz.
Hypothesis IOz : same_io md0 mdl.
Hypothesis HWZ : forall mat, wz_facts grow z Wz (with_vm_backing (m_vm_lazy mdl) mat mdl).
Hypothesis HOUT : forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb) ->
~ (grow = true /\ QSv <= bv_unsigned x < QSv + 131072) -> w_H Wz x = w_H W x.
Theorem LEAF_S : forall regs' mem' memD mat,
Wf (as_universe B) (SFS grow z) /\ qtight (SFS grow z) ->
fin_facts grow z Wz regs' mem' memD ->
malloc_leaf tfibsegs B ly S W regs0 mem0 md0 n (ck_user KSc, SFS grow z) Wz
(mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdl) mat mdl)).
Proof.
intros regs' mem' memD mat MP HF. set (mdf := with_vm_backing (m_vm_lazy mdl) mat mdl).
pose proof (HWZ mat) as HW. fold mdf in HW.
pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ. pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _).
pose proof Hidx as HI. pose proof Hres as [HRS _]. destruct Hsp as (S1 & S2 & S3 & S4). pose proof (SH_hull mb) as (H1 & H2 & H3 & _).
pose proof HW as [MONf _ _ _ _ _ _ _ _ _ GAP]. pose proof blocks_facts as (NBhi & SBhi & _).
pose proof HF as [_ _ _ _ _ fMEQF fPRS _ _ _ _ _ fR10 fRCS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
exists lyF, regs', mem', mdf.
split. { unfold cfg_at, raZ, YG0d_w.w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [| split; [| exact (proj2 MP)]].
2:{ rewrite fR10. cbn [fst]. unfold ck_user. cbn [YG00.ck_beg KSc AFib_w.KS padd sptr_addr sptr_exp aeval].
change (YG00.ck_rz (AFib_w.KS S n)) with (ck_rz KSc). rewrite KR, lyF_sec. unfold Uv, YG0d_w.w64, w64, kPage. f_equal; zlia. }
split; [exact (S_AR_final grow z Wz mdf regs' mem' memD HAR Hgrow MP HF HW)|].
split; [exact lyF_le|].
split; [exact LEz|].
split. { intros r Hr. apply fRCS. unfold acallee_saved in Hr.
assert (H18 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by zlia.
clear - H18 MZ.
assert (E5 : forall k : Z, 0 <= k < 32 -> forall b : bv 5, bv_unsigned b = k -> Z_to_bv 5 k = b) by (intros k Hk b Hb; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 5) with 32; rewrite Z.mod_small by zlia; symmetry; exact Hb).
destruct H18 as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
[ rewrite (E5 2 ltac:(zlia) 2%bv eq_refl) | rewrite (E5 3 ltac:(zlia) 3%bv eq_refl) | rewrite (E5 4 ltac:(zlia) 4%bv eq_refl)
| rewrite (E5 8 ltac:(zlia) 8%bv eq_refl) | rewrite (E5 9 ltac:(zlia) 9%bv eq_refl) | rewrite (E5 18 ltac:(zlia) 18%bv eq_refl)
| rewrite (E5 19 ltac:(zlia) 19%bv eq_refl) | rewrite (E5 20 ltac:(zlia) 20%bv eq_refl) | rewrite (E5 21 ltac:(zlia) 21%bv eq_refl)
| rewrite (E5 22 ltac:(zlia) 22%bv eq_refl) | rewrite (E5 23 ltac:(zlia) 23%bv eq_refl) | rewrite (E5 24 ltac:(zlia) 24%bv eq_refl)
| rewrite (E5 25 ltac:(zlia) 25%bv eq_refl) | rewrite (E5 26 ltac:(zlia) 26%bv eq_refl) | rewrite (E5 27 ltac:(zlia) 27%bv eq_refl) ];
cbn [In]; tauto. }
split. { unfold mdf. eapply YG0b_w.same_io_trans; [exact IOz | apply YG0b_w.same_io_with_vm_backing]. }
split; [| exact fPRS].
intros a Ra NO NO' NS NE. cbn [fst] in NE.
assert (NE' : ~ (Uv <= a < Uv + n)).
{ intros Hu. apply NE. split; [discriminate|]. unfold ck_user. cbn [YG00.ck_beg KSc AFib_w.KS padd sptr_addr sptr_exp aeval].
change (YG00.ck_rz (AFib_w.KS S n)) with (ck_rz KSc). rewrite KR, RS, lyF_sec. unfold Uv in Hu. unfold kPage. clear - Hu MZ. zlia. }
assert (NST : ~ (sp0 - ASTACK <= a < sp0)) by (intros Hs; apply NS; unfold ascratch, spZ; left; exact Hs).
set (x := Z_to_bv 64 a). assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ra).
assert (MEQa : mem' x = mem0 x).
{ apply fMEQF; rewrite Ux.
- intros Hw. unfold WIN, WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
+ exact (NST Hw).
+ exact (NO (OWN_T a Hw)).
+ exact (NO (OWN_I a Hw)).
+ apply NO, OWN_Q. unfold QSv in Hw. clear - Hw HI HRS MZ. unfold Qb in *. unfold kPtrArrayResv, kMaxNumChunks in *. zlia.
+ exact (NO' (NEWOWN grow z GAP a Hw NE')).
+ exact (NO (OWN_SH GAP a Hw)).
- intros [_ Hq]. apply NO, OWN_Q. unfold QR in Hq. clear - Hq HRS HI MZ. unfold Qb in *. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. zlia.
- intros [Hs|Hd]; [apply NST; clear - Hs MZ; unfold DEP_STK, ASTACK in *; zlia | exact (NO (OWN_D a Hd))]. }
destruct (w_H W x) eqn:EhW.
-
destruct (w_H Wz x) eqn:EhZ.
+ unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ. reflexivity.
+ exfalso. destruct (zr_dec mb (mb + MSv) a) as [D1|D1]; [exact (NO' (NEWOWN grow z GAP a D1 NE'))|].
destruct (zr_dec (SHLO mb) (SHHI mb) a) as [D2|D2].
{ apply NO. apply (OWN_BANDhid HAR a); [| subst x; exact EhW]. clear - D2 H1 H2 SM1 SM2 H3 M1 M2 M3 Z8 SMA MZ.
unfold SHLO, SHHI, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(zlia)).
pose proof (Z.div_mod (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)).
pose proof (Z.div_mod MSv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)). zlia. }
destruct grow eqn:Eg.
* destruct (zr_dec QSv (QSv + 131072) a) as [D3|D3].
{ apply NO, OWN_Q. pose proof (proj1 Hgrow eq_refl) as EIR. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ (proj1 MP))) as WR.
pose proof (SF_parts true z) as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _). rewrite Rarr, Rres in WR.
unfold QSv in D3. clear - D3 HI HRS EIR WR MZ. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. zlia. }
rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | rewrite Ux; intros [_ Hq]; exact (D3 Hq)].
* rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | intros [E _]; discriminate E].
-
pose proof (MONf x EhW) as EhZ. unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ, MEQa. reflexivity.
Qed.
End h.
End f.
End d.
