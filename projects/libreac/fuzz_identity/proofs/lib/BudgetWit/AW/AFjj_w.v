(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFjj.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFjj.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AB1h_w AFjm_w AFid_w AFie_w AFjv_w AFjw_w AFjx_w AFjh_w AFjn_w AFib_w.
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
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Ltac s_station HR ss' :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in
pose proof (at_S_eq Wx md X P ss ss' W' c' HR ltac:(vm_compute; reflexivity)) as H2; clear HR; rename H2 into HR end.
Local Ltac s_noconds HR :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let H2 := fresh "HR" in pose proof (at_S_noconds Wx md X P ss W' c' HR) as H2; clear HR; rename H2 into HR end.
Local Ltac s_runN HR tbl tblok stop ss' HX HP :=
lazymatch type of HR with at_S ?Wx ?md ?X ?P ?ss ?W' ?c' =>
let st := eval vm_compute in (snd (sym_run_toN_sh tfibsegs tbl FUEL stop ss)) in
eapply SRr_bind;
[ eapply (at_S_runN Wx tbl tblok stop md X P ss ss' st W' c' HR);
[ vm_compute; reflexivity | exact I | exact HX | vm_compute; reflexivity | exact HP | vm_compute; reflexivity ]
| clear HR; let W2 := fresh "W" in let c2 := fresh "c" in intros W2 c2 _ HR ] end.
Definition PNULL (m : word -> option byte) : Prop :=
PBUF m /\ val_mem tfibsegs (mrestrict (w_H W) m) TFIB_OOM 1 1 /\ val_mem tfibsegs (mrestrict (w_H W) m) TFIB_ERRNO 4 12.
Definition PNULLX (m : word -> option byte) : Prop :=
PNULL m /\
(val_mem tfibsegs (mrestrict (w_H W) m) (T + t_unwinding) 1 0 /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_reserved) 8 res /\
val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_n) 8 idx /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_mutex) 4 0 /\
(forall a, WINT a -> apresent (w_H W) m a) /\ (forall a, WINI a -> aview tfibsegs (w_H W) m a <> None)).
Lemma tail_lits_apart : forall r, In (skel r) SKEL_TAIL -> YP09.r_base r = None ->
(YP09.r_hi r <= TFIB_OOM \/ TFIB_OOM + 2 <= YP09.r_lo r) /\ (YP09.r_hi r <= TFIB_ERRNO \/ TFIB_ERRNO + 4 <= YP09.r_lo r).
Proof.
clearP. intros r Hin Hb. destruct r as [bs lo hi wlo whi cs]. cbn [YP09.r_base] in Hb. subst bs. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in *.
let sk := eval vm_compute in SKEL_TAIL in change SKEL_TAIL with sk in Hin. cbn [In] in Hin. unfold TFIB_OOM, TFIB_ERRNO.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [first [discriminate Hin | injection Hin as <- <- <- <-; clear; zlia] |] | False => destruct Hin end.
Qed.
Lemma segR : forall W' c',
at_S W md0 WINP PBUF (resume S_N (SLit ENOMEM_RETv) (ss_mem S_N) (ss_facts S_N)) W' c' ->
SRr tfibsegs W' c' (at_RETS W (w64 0) md0 WINPN PNULLX).
Proof.
clearP. intros W1 c1 HR. pose proof PBUF_stableN as HP. pose proof WIN1N_WINPN as HX.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _).
assert (OOM1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (TFIB_OOM + 1) 1 1) by (apply cell_lit; vm_compute; reflexivity).
s_noconds HR.
apply (at_S_weaken W md0 WINP WINPN PBUF PBUF _ W1 c1) in HR; [| intros a Ha; left; exact Ha | intros m Hm; exact Hm].
apply (at_S_app W md0 WINPN PBUF _ W1 c1 NREGS) in HR; [| reflexivity |].
2:{ intros E' m HE MEQ PRS HPm HM. pose proof (proj1 HE) as HEn.
assert (OOM1' : val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_OOM + 1) 1 1).
{ eapply val_mem_frame; [|exact OOM1]. intros k Hk. apply MEQ. rewrite unsigned_lit_small by (unfold TFIB_OOM; zlia).
pose proof BSLv_range as HB. clear - Hk F1 F2 S1 T7 HB. unfold WINPN, WINP, WINT, WINI. numconst. unfold TFIB_OOM, TFIB_ERRNO, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. try unfold T in *. zlia. }
split; [|split].
- unfold NREGS. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ unfold region_ok, lit1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; zlia|]. split; [unfold TFIB_OOM; zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; zlia | cbn; zlia |]. rewrite Z.add_0_l. exact OOM1'.
+ unfold region_ok, oomR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_OOM; zlia|]. split; [unfold TFIB_OOM; zlia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply img_rw_writable. unfold TFIB_OOM in *. zlia.
+ unfold region_ok, errR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold TFIB_ERRNO; zlia|]. split; [unfold TFIB_ERRNO; zlia|]. split; [|apply Forall_nil]. intros o Ho. rewrite Z.add_0_l. apply img_rw_writable. unfold TFIB_ERRNO in *. zlia.
- unfold NREGS, lit1, oomR, errR. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. clear. unfold TFIB_OOM, TFIB_ERRNO. repeat split; zlia.
- intros r1 r2 Hr1 Hr2.
assert (B2 : base_val E' (Some 2%nat) = sp0) by (cbn [base_val]; rewrite (HEn 2%nat ltac:(unfold sHAV; zlia)), E2; reflexivity).
assert (L2' : YP09.r_base r2 = None /\ ((YP09.r_lo r2 = TFIB_OOM + 1 /\ YP09.r_hi r2 = TFIB_OOM + 2) \/ (YP09.r_lo r2 = TFIB_OOM /\ YP09.r_hi r2 = TFIB_OOM + 1) \/ (YP09.r_lo r2 = TFIB_ERRNO /\ YP09.r_hi r2 = TFIB_ERRNO + 4))).
{ unfold NREGS, lit1, oomR, errR in Hr2. destruct Hr2 as [<-|[<-|[<-|[]]]]; cbn; [split; [reflexivity|left; zlia] | split; [reflexivity|right; left; zlia] | split; [reflexivity|right; right; zlia]]. }
destruct L2' as [Hb2 L2].
unfold extent_disjoint. rewrite Hb2. cbn [base_val].
lazymatch type of Hr1 with In _ ?l =>
let m3 := eval vm_compute in (firstn 3 l) in
let tl3 := eval vm_compute in (skipn 3 l) in
assert (SPLIT : In r1 m3 \/ In (skel r1) SKEL_TAIL)
by (change l with (m3 ++ tl3) in Hr1; apply in_app_iff in Hr1 as [Hr1|Hr1]; [left; exact Hr1 | right];
apply (in_map skel) in Hr1; replace (map skel tl3) with SKEL_TAIL in Hr1 by (vm_compute; reflexivity); exact Hr1) end.
clear Hr1. destruct SPLIT as [Hr1|Hr1].
+ destruct Hr1 as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_lo YP09.r_hi]; rewrite B2;
clear - L2 S1 T7 U2; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_OOM, TFIB_ERRNO, kHighMemBeg, ASTACK, IFRAME in *; unfold sp0 in *; zlia.
+ pose proof (tail_ext_ok E' r1 HEn Hr1) as (X1 & X2 & X3 & X4 & X5 & X6).
destruct (YP09.r_base r1) as [b|] eqn:Eb.
*
clear X1 X2 X3 X4 X5 X6. destruct r1 as [bs lo hi wlo whi cs]. cbn [YP09.r_base] in Eb. subst bs. unfold skel in Hr1.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hr1 |- *.
let sk := eval vm_compute in SKEL_TAIL in change SKEL_TAIL with sk in Hr1. cbn [In] in Hr1.
repeat match type of Hr1 with _ \/ _ => destruct Hr1 as [Hr1|Hr1]; [first [discriminate Hr1 | injection Hr1 as <- <- <- <- <-] |] | False => destruct Hr1 end.
all: pose proof BSLv_range as HB; cbn [base_val]; rewrite ?(HEn 32%nat ltac:(unfold sHAV; zlia)), ?(HEn 33%nat ltac:(unfold sHAV; zlia)), ?(HEn 55%nat ltac:(unfold sHAV; zlia)); rewrite ?EaT, ?EaC, ?EaBSL; unfold w64;
rewrite unsigned_lit_small by (clear - F1 F2 F7 F8 HB; numconst; unfold TFIB_INST in *; try unfold T in *; zlia); clear - L2 F1 F7 HB; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_OOM, TFIB_ERRNO, kHighMemBeg, TFIB_INST in *; try unfold T in *; zlia.
* pose proof (tail_lits_apart r1 Hr1 Eb) as [A1 A2]. cbn [base_val]. clear - L2 A1 A2. unfold TFIB_OOM, TFIB_ERRNO in *. zlia. }
s_station HR S_R0.
s_runN HR tfibtbl_rtC tfibtbl_rtC_ok 0x36424 S_R1 HX HP.
s_runN HR tfibtbl_rtA tfibtbl_rtA_ok 0x52ed8 S_RET HX HP.
apply (at_S_facts W md0 WINPN PBUF (fun m => (val_mem tfibsegs (mrestrict (w_H W) m) TFIB_OOM 1 1 /\ val_mem tfibsegs (mrestrict (w_H W) m) TFIB_ERRNO 4 12) /\
(val_mem tfibsegs (mrestrict (w_H W) m) (T + t_unwinding) 1 0 /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_reserved) 8 res /\
val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_n) 8 idx /\ val_mem tfibsegs (mrestrict (w_H W) m) (TFIB_INST + o_sec_mutex) 4 0 /\
(forall a, WINT a -> apresent (w_H W) m a) /\ (forall a, WINI a -> aview tfibsegs (w_H W) m a <> None))) S_RET) in HR.
2:{ intros E' ms HE HS. pose proof (proj1 HE) as HEn. pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof BSLv_range as HB.
assert (UT : bv_unsigned (ew E' 32) = T) by (rewrite (HEn 32%nat ltac:(unfold sHAV; zlia)), EaT; unfold w64; apply unsigned_lit_small; clear - F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia).
assert (UBSL : bv_unsigned (ew E' 55) = BSLv) by (rewrite (HEn 55%nat ltac:(unfold sHAV; zlia)), EaBSL; unfold w64; apply unsigned_lit_small; unfold TFIB_INST in *; zlia).
split; [split; [memv HS 61%nat 0%nat; [reflexivity | reflexivity | zlia] | memv HS 62%nat 0%nat; [reflexivity | reflexivity | zlia]]|].
split; [memv HS 41%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite UT; unfold t_unwinding; zlia | reflexivity | zlia]|].
split; [memv HS 49%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | rewrite sv_denot_SOff0, (HEn 40%nat ltac:(unfold sHAV; zlia)), EaRES; reflexivity | unfold kMaxNumChunks in *; zlia]|].
split; [memv HS 50%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | rewrite sv_denot_SOff0, (HEn 41%nat ltac:(unfold sHAV; zlia)), EaNCH; reflexivity | unfold kMaxNumChunks in *; zlia]|].
split; [memv HS 53%nat 0%nat; [cbn [base_val YP09.r_base]; reflexivity | reflexivity | zlia]|].
split.
- intros a Hw. unfold WINT in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
+ destruct (Z_lt_le_dec a (T + 2800)) as [H28|H28].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 40%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
* eapply (st_ok_window_apresent_off (w_H W) E' _ _ 42%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw H28 F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 43%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 44%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
+ eapply (st_ok_window_apresent_off (w_H W) E' _ _ 41%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UT; unfold t_unwinding in *; zlia | off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, t_unwinding in *; clear - Hw F1 F2; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in *; try unfold T in *; zlia) ].
- intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha HB; unfold WINI, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; zlia).
apply (AFib_w.writable_visible (w_H W) (ms_mem ms) a Ra). unfold WINI in Ha.
destruct Ha as [Hw|[Hw|[Hw|[Hw|Hw]]]].
+ destruct (Z_lt_le_dec a (TFIB_INST + 120)) as [A1|A1]; [|destruct (Z_lt_le_dec a (TFIB_INST + 128)) as [A2|A2]].
* eapply (st_ok_window_writable (w_H W) E' _ _ 49%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_reserved in *; zlia].
* eapply (st_ok_window_writable (w_H W) E' _ _ 50%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST in *; zlia].
* eapply (st_ok_window_writable (w_H W) E' _ _ 51%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_sorted in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 52%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_stats in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 59%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite UBSL; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 53%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; unfold TFIB_INST, o_sec_mutex in *; zlia].
+ eapply (st_ok_window_writable (w_H W) E' _ _ 54%nat _ a HS); [reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; zlia]. }
apply (at_S_weaken W md0 WINPN WINPN _ PNULLX S_RET) in HR; [| intros a Ha; exact Ha | intros m [H1 [H2 H3]]; exact (conj (conj H1 H2) H3)].
change (w64 0) with (sv_denot E0 (SLit 0)).
eapply (at_S_ret W md0 WINPN PNULLX S_RET _ _ (SLit 0) HR); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity |].
repeat constructor.
Qed.
End f.
End d.
