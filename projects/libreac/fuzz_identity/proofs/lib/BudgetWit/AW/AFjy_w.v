(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFjy.v, with its module paths and addresses changed; 4 of its 1786 lines of code are new or changed and 4 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFjy.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFjv_w AFjw_w AFjx_w AFjh_w AFjn_w AFjo_w AFjk_w AFjl_w AFjp_w AFjq_w AFjs_w AFju_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Section b0.
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
Local Ltac clearP := try clear Hmap_apart; try clear Hmap.
Local Open Scope am_scope.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let WF := am_wf B ly S rd0 HARm.
Definition lyF : alayout := set_ly_sec ly (rS S) mb.
Definition SFS (grow : bool) (z : Z) : astate := sfinal S n tr z MSv NDv grow.
Definition KSc : chunk := KS S n.
Lemma lyF_le : layout_le (length (st_secs S)) ly lyF.
Proof. clearP. unfold lyF, rS. apply set_ly_sec_le. Qed.
Lemma lyF_sec : ly_sec lyF (rS S) = mb.
Proof. clearP. unfold lyF, set_ly_sec. cbn. rewrite PeanoNat.Nat.eqb_refl. reflexivity. Qed.
Lemma lyF_eqs : ly_prim lyF = ly_prim ly /\ ly_space lyF = ly_space ly /\ ly_Q lyF = Qb /\ ly_T lyF = T /\ ly_C lyF = ly_C ly /\ ly_F lyF = ly_F ly /\
ly_NB lyF = ly_NB ly /\ ly_SB lyF = ly_SB ly /\ ly_top lyF = ly_top ly /\ ly_stk_lo lyF = ly_stk_lo ly /\ ly_stk_hi lyF = ly_stk_hi ly /\
ly_tsd lyF = ly_tsd ly /\ ly_tr0 lyF = ly_tr0 ly /\ ly_extra lyF = ly_extra ly /\ ly_D lyF = ly_D ly /\ ly_vis0 lyF = ly_vis0 ly.
Proof. clearP. unfold lyF, set_ly_sec. cbn. repeat split; reflexivity. Qed.
Lemma lyF_ok : layout_ok lyF.
Proof. unfold lyF. apply set_ly_sec_ok. exact LY. Qed.
Lemma sizes_model : needed_size n = NDv /\ sec_map_size n = MSv /\ req_size n = n /\ rz_size n = 2048 /\ from_primary n = false /\
ck_n KSc = n /\ ck_rz KSc = 2048 /\ ck_extent KSc = MSv - 4096 /\ ck_req KSc = n /\ ck_beg KSc = PSec (rS S) 4096 /\ ck_state KSc = CAllocated.
Proof.
clearP. pose proof Nrange as NR. unfold MALLOC_MAX in NR.
assert (RZ : rz_size n = 2048).
{ unfold rz_size, rz_log. rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
(proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by zlia. reflexivity. }
assert (RS : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); zlia).
assert (R8 : rounded_size n = R8v) by (unfold rounded_size, round_up, R8v; rewrite Z.max_l by zlia; replace (n + 8 - 1) with (n + 7) by zlia; reflexivity).
assert (FP : from_primary n = false) by (unfold from_primary, needed_primary; rewrite R8, RZ; apply Z.leb_gt; unfold kMaxSize, R8v; pose proof (Z.div_mod (n+7) 8 ltac:(zlia)); pose proof (Z.mod_pos_bound (n+7) 8 ltac:(zlia)); zlia).
assert (ND : needed_size n = NDv) by (unfold needed_size, needed_primary, NDv; rewrite FP, R8, RZ; zlia).
assert (MS : sec_map_size n = MSv) by (unfold sec_map_size, round_up, MSv, kPage; rewrite ND; replace (NDv + 4096 - 1) with (NDv + 4095) by zlia; reflexivity).
unfold KSc, KS, ck_n, ck_rz, ck_extent, ck_req, ck_beg, ck_state. cbn [YG00.ck_req YG00.ck_beg YG00.ck_state].
rewrite RS, RZ, FP, MS. unfold kPage. repeat split; try reflexivity; zlia.
Qed.
Lemma val_mem_cell : forall (Hh : word -> bool) mem e (w : nat) e' lyx,
val_mem tfibsegs (mrestrict Hh mem) (aeval B lyx e) w (aeval B lyx e') -> cell_holds B lyx (aview tfibsegs Hh mem) (ACell e w (AV e')).
Proof.
clearP. intros Hh mem e w e' lyx HV k Hk. cbn [c_at c_val c_w]. unfold aview. rewrite (HV k Hk). cbn [option_map].
rewrite <- le_byte_eq. rewrite unsigned_lit_small8; [reflexivity|]. unfold YG0f.le_byte. apply Z.mod_pos_bound. zlia.
Qed.
Lemma le_byte_1_0 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
clearP. intros x Hx. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0)%Z with 0.
rewrite Z.shiftr_0_r, Z.mod_mod by zlia. apply Z.mod_small. exact Hx.
Qed.
Lemma find_chunk_at_app1 : forall lyx l1 l2 g k, find_chunk_at B lyx l1 g = Some k -> find_chunk_at B lyx (l1 ++ l2) g = Some k.
Proof.
clearP. intros lyx l1 l2 g k. induction l1 as [|k1 t IH]; intros H; [discriminate H|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [exact H | exact (IH H)].
Qed.
Lemma find_chunk_at_app2 : forall lyx l1 l2 g, find_chunk_at B lyx l1 g = None -> find_chunk_at B lyx (l1 ++ l2) g = find_chunk_at B lyx l2 g.
Proof.
clearP. intros lyx l1 l2 g. induction l1 as [|k1 t IH]; intros H; [reflexivity|]. cbn [find_chunk_at app] in *.
destruct ((ck_base B lyx k1 <=? g) && (g <? ck_base B lyx k1 + ck_extent k1)); [discriminate H | exact (IH H)].
Qed.
Lemma In_combine_seq_app : forall {X : Type} (l0 : list X) (x : X) s p, In p (combine (seq s (length l0)) l0) -> In p (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
clearP. intros X l0. induction l0 as [|y t IH]; intros x s p H; [destruct H|]. cbn [length combine seq app Nat.add] in *.
destruct H as [H|H]; [left; exact H | right]. apply IH. exact H.
Qed.
Lemma combine_seq_last : forall {X : Type} (l0 : list X) (x : X) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof.
clearP. intros X l0. induction l0 as [|y t IH]; intros x s; cbn [length combine seq app Nat.add].
- rewrite Nat.add_0_r. left. reflexivity.
- right. replace (s + Datatypes.S (length t))%nat with (Datatypes.S s + length t)%nat by zlia. apply IH.
Qed.
Lemma in_combine_seq : forall {X : Type} (l : list X) s i x, In (i, x) (combine (seq s (length l)) l) -> nth_error l (i - s) = Some x /\ (s <= i < s + length l)%nat.
Proof.
clearP. intros X l. induction l as [|y t IH]; intros s i x H; [destruct H|]. cbn [length seq combine] in H.
destruct H as [H|H].
- injection H as <- <-. rewrite Nat.sub_diag. cbn. split; [reflexivity | zlia].
- destruct (IH _ _ _ H) as [E R]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by zlia. cbn [nth_error length]. split; [exact E | zlia].
Qed.
Lemma combine_seq_in : forall {X : Type} (l : list X) s i x, nth_error l (i - s) = Some x -> (s <= i)%nat -> In (i, x) (combine (seq s (length l)) l).
Proof.
clearP. intros X l. induction l as [|y t IH]; intros s i x E Hs; [destruct (i - s)%nat; discriminate E|]. cbn [length seq combine].
destruct (Nat.eq_dec i s) as [->|Hne].
- rewrite Nat.sub_diag in E. cbn in E. injection E as <-. left. reflexivity.
- right. apply IH; [|zlia]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) in E by zlia. cbn in E. exact E.
Qed.
Lemma index_of_app_old : forall (l : list nat) (x r : nat) s, In r l -> index_of (l ++ [x]) r s = index_of l r s.
Proof.
clearP. induction l as [|y t IH]; intros x r s Hr; [destruct Hr|]. cbn [index_of app]. destruct (Nat.eqb y r) eqn:E; [reflexivity|].
destruct Hr as [->|Hr]; [rewrite Nat.eqb_refl in E; discriminate E|]. exact (IH x r (Datatypes.S s) Hr).
Qed.
Lemma index_ofZ_app_old : forall (l : list nat) (x r : nat), In r l -> index_ofZ (l ++ [x]) r = index_ofZ l r.
Proof. clearP. intros l x r Hr. unfold index_ofZ. rewrite (index_of_app_old l x r 0 Hr). reflexivity. Qed.
Lemma index_of_app_new : forall (l : list nat) (x : nat) s, ~ In x l -> index_of (l ++ [x]) x s = Some (s + length l)%nat.
Proof.
clearP. induction l as [|y t IH]; intros x s Hx; cbn [index_of app length].
- rewrite Nat.eqb_refl, Nat.add_0_r. reflexivity.
- destruct (Nat.eqb_spec y x) as [E|E]; [exfalso; apply Hx; left; exact E|]. rewrite (IH x (Datatypes.S s) ltac:(intros H; apply Hx; right; exact H)). f_equal. zlia.
Qed.
Lemma index_ofZ_app_new : forall (l : list nat) (x : nat), ~ In x l -> index_ofZ (l ++ [x]) x = Z.of_nat (length l).
Proof. clearP. intros l x Hx. unfold index_ofZ. rewrite (index_of_app_new l x 0 Hx). cbn [Nat.add]. reflexivity. Qed.
Record fin_facts (grow : bool) (z : Z) (Wz : world tfibsegs) (regs' : bvmap 5 word) (mem' memD : word -> option byte) : Prop := mkFin {
f_AOK : aok S (KDepot tr) z;
f_DEPD : depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs (w_H Wz) memD);
f_CSTD : Forall (cell_holds B ly (aview tfibsegs (w_H Wz) memD)) (as_const B ly);
f_PRD : forall a, DZONE a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a;
f_EQD : forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x;
f_MEQF : forall x : word, ~ WIN (bv_unsigned x) -> ~ (grow = true /\ QR (bv_unsigned x)) -> ~ DX (bv_unsigned x) -> mem' x = mem0 x;
f_PRS : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wz) mem' a;
f_PRmap : forall a, mb <= a < mb + MSv -> apresent (w_H Wz) mem' a;
f_PRsh : forall a, SMv <= a < SMv + MSv / 8 -> apresent (w_H Wz) mem' a;
f_PRq : grow = true -> forall a, QR a -> apresent (w_H Wz) mem' a;
f_PRW : forall a, WINT a \/ (QSv <= a < QSv + 8) -> apresent (w_H Wz) mem' a;
f_VISW : forall a, WINI a -> aview tfibsegs (w_H Wz) mem' a <> None;
f_R10 : getr regs' 10 = w64 Uv;
f_RCS : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r;
f_Vsh : forall x : word, (SMv <= bv_unsigned x < SMv + 768 \/ SHBv + UEv / 8 <= bv_unsigned x < SMv + MSv / 8) -> mem' x = Some (Z_to_bv 8 250);
f_Vzs : forall x : word, SMv + 768 <= bv_unsigned x < SMv + 768 + N8D / 8 -> mem' x = Some (Z_to_bv 8 0);
f_Vpb : n mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H Wz) mem') PBv 1 (n mod 8);
f_Vunw : val_mem tfibsegs (mrestrict (w_H Wz) mem') (T + t_unwinding) 1 0;
f_Vres : val_mem tfibsegs (mrestrict (w_H Wz) mem') (TFIB_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res);
f_Vnch : val_mem tfibsegs (mrestrict (w_H Wz) mem') (TFIB_INST + o_sec_n) 8 (idx + 1);
f_Vmtx : val_mem tfibsegs (mrestrict (w_H Wz) mem') (TFIB_INST + o_sec_mutex) 1 0;
f_Vpad : forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wz) mem' (TFIB_INST + o_sec_mutex + k) = Some 0;
f_Vslot : val_mem tfibsegs (mrestrict (w_H Wz) mem') QSv 8 mb;
f_Vh0 : val_mem tfibsegs (mrestrict (w_H Wz) mem') mb 8 mb;
f_Vh8 : val_mem tfibsegs (mrestrict (w_H Wz) mem') (mb + 8) 8 MSv;
f_Vh16 : val_mem tfibsegs (mrestrict (w_H Wz) mem') (mb + 16) 8 NDv;
f_Vh24 : val_mem tfibsegs (mrestrict (w_H Wz) mem') (mb + 24) 8 idx;
f_Vmag : val_mem tfibsegs (mrestrict (w_H Wz) mem') Kv 8 0xCC6E96B9CC6E96B9;
f_Vbk : val_mem tfibsegs (mrestrict (w_H Wz) mem') (Kv + 8) 8 (Uv - 16);
f_Vst : val_mem tfibsegs (mrestrict (w_H Wz) mem') (Uv - 16) 1 2;
f_Vb1 : val_mem tfibsegs (mrestrict (w_H Wz) mem') (Uv - 15) 1 17;
f_Vb2 : val_mem tfibsegs (mrestrict (w_H Wz) mem') (Uv - 14) 2 0;
f_Vn : val_mem tfibsegs (mrestrict (w_H Wz) mem') (Uv - 12) 4 n;
f_Vfill : forall x : word, Uv <= bv_unsigned x < Uv + 4096 -> mem' x = Some (Z_to_bv 8 190) }.
Record wz_facts (grow : bool) (z : Z) (Wz : world tfibsegs) (mdf : Model) : Prop := mkWz {
w_MONf : forall x : word, w_H W x = false -> w_H Wz x = false;
w_VISmap : forall x : word, mb <= bv_unsigned x < mb + MSv -> w_H Wz x = false;
w_VISsh : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb -> w_H Wz x = false;
w_VISq : grow = true -> forall x : word, QR (bv_unsigned x) -> w_H Wz x = false;
w_ABf : A_bytes (w_A Wz) = A_bytes (w_A W) + MSv + (SHHI mb - SHLO mb) + (if grow then 131072 else 0);
w_HINC : forall i, In i (w_A W) -> In i (w_A Wz);
w_AMAP : In (mb, mb + MSv) (w_A Wz);
w_AHULL : In (SHLO mb, SHHI mb) (w_A Wz);
w_LEDf : ALedger tfibsegs lyF (SFS grow z) mdf;
w_MWf : amwf mdf;
w_GAPART : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) }.
Section c0.
Variables (grow : bool) (z : Z) (Wz : world tfibsegs) (mdf : Model) (regs' : bvmap 5 word) (mem' memD : word -> option byte).
Let rd' : reader := aview tfibsegs (w_H Wz) mem'.
Let rdD : reader := aview tfibsegs (w_H Wz) memD.
Let m' := mrestrict (w_H Wz) mem'.
Let SF : astate := SFS grow z.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Hgrow : grow = true <-> idx = res.
Hypothesis MP : Wf (as_universe B) SF /\ qtight SF.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HFIN : fin_facts grow z Wz regs' mem' memD.
Hypothesis HWZ : wz_facts grow z Wz mdf.
Let JUNK : forall ly1 ly2, as_junk B ly1 = as_junk B ly2 := fun ly1 ly2 => ts_junk_ly B TS ly2 ly1.
Let MONf := w_MONf _ _ _ _ HWZ. Let VISmap := w_VISmap _ _ _ _ HWZ. Let VISsh := w_VISsh _ _ _ _ HWZ. Let VISq := w_VISq _ _ _ _ HWZ.
Let ABf := w_ABf _ _ _ _ HWZ. Let HINC := w_HINC _ _ _ _ HWZ. Let AMAP := w_AMAP _ _ _ _ HWZ. Let AHULL := w_AHULL _ _ _ _ HWZ. Let LEDf := w_LEDf _ _ _ _ HWZ.
Let MWf := w_MWf _ _ _ _ HWZ. Let GAPART := w_GAPART _ _ _ _ HWZ.
Let AOK := f_AOK _ _ _ _ _ _ HFIN. Let DEPD : depot_mem_ok B ly (depot_after z tr S) rdD := f_DEPD _ _ _ _ _ _ HFIN.
Let CSTD : Forall (cell_holds B ly rdD) (as_const B ly) := f_CSTD _ _ _ _ _ _ HFIN.
Let PRD := f_PRD _ _ _ _ _ _ HFIN. Let EQD := f_EQD _ _ _ _ _ _ HFIN. Let MEQF := f_MEQF _ _ _ _ _ _ HFIN.
Let PRS := f_PRS _ _ _ _ _ _ HFIN. Let PRmap := f_PRmap _ _ _ _ _ _ HFIN. Let PRsh := f_PRsh _ _ _ _ _ _ HFIN. Let PRq := f_PRq _ _ _ _ _ _ HFIN. Let PRW := f_PRW _ _ _ _ _ _ HFIN.
Let VISW : forall a, WINI a -> rd' a <> None := f_VISW _ _ _ _ _ _ HFIN.
Let R10 := f_R10 _ _ _ _ _ _ HFIN. Let RCS := f_RCS _ _ _ _ _ _ HFIN.
Let Vsh := f_Vsh _ _ _ _ _ _ HFIN. Let Vzs := f_Vzs _ _ _ _ _ _ HFIN. Let Vpb : n mod 8 <> 0 -> val_mem tfibsegs m' PBv 1 (n mod 8) := f_Vpb _ _ _ _ _ _ HFIN.
Let Vunw : val_mem tfibsegs m' (T + t_unwinding) 1 0 := f_Vunw _ _ _ _ _ _ HFIN.
Let Vres : val_mem tfibsegs m' (TFIB_INST + o_sec_reserved) 8 (if grow then res + kPtrArrayEntriesPerCommit else res) := f_Vres _ _ _ _ _ _ HFIN.
Let Vnch : val_mem tfibsegs m' (TFIB_INST + o_sec_n) 8 (idx + 1) := f_Vnch _ _ _ _ _ _ HFIN.
Let Vmtx : val_mem tfibsegs m' (TFIB_INST + o_sec_mutex) 1 0 := f_Vmtx _ _ _ _ _ _ HFIN.
Let Vpad : forall k, 1 <= k < 4 -> rd' (TFIB_INST + o_sec_mutex + k) = Some 0 := f_Vpad _ _ _ _ _ _ HFIN.
Let Vslot : val_mem tfibsegs m' QSv 8 mb := f_Vslot _ _ _ _ _ _ HFIN.
Let Vh0 : val_mem tfibsegs m' mb 8 mb := f_Vh0 _ _ _ _ _ _ HFIN.
Let Vh8 : val_mem tfibsegs m' (mb + 8) 8 MSv := f_Vh8 _ _ _ _ _ _ HFIN.
Let Vh16 : val_mem tfibsegs m' (mb + 16) 8 NDv := f_Vh16 _ _ _ _ _ _ HFIN.
Let Vh24 : val_mem tfibsegs m' (mb + 24) 8 idx := f_Vh24 _ _ _ _ _ _ HFIN.
Let Vmag : val_mem tfibsegs m' Kv 8 0xCC6E96B9CC6E96B9 := f_Vmag _ _ _ _ _ _ HFIN.
Let Vbk : val_mem tfibsegs m' (Kv + 8) 8 (Uv - 16) := f_Vbk _ _ _ _ _ _ HFIN.
Let Vst : val_mem tfibsegs m' (Uv - 16) 1 2 := f_Vst _ _ _ _ _ _ HFIN.
Let Vb1 : val_mem tfibsegs m' (Uv - 15) 1 17 := f_Vb1 _ _ _ _ _ _ HFIN.
Let Vb2 : val_mem tfibsegs m' (Uv - 14) 2 0 := f_Vb2 _ _ _ _ _ _ HFIN.
Let Vn : val_mem tfibsegs m' (Uv - 12) 4 n := f_Vn _ _ _ _ _ _ HFIN.
Let Vfill := f_Vfill _ _ _ _ _ _ HFIN.
Let MA : ARm B ly S rd0 := proj1 HAR.
Definition XC (a : Z) : Prop :=
WINT a \/ WINI a \/ (QSv <= a < QSv + 8) \/ (mb <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8) \/ DZONE a \/ (grow = true /\ QR a).
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. clear. intros lo hi a. zlia. Qed.
Lemma or_dec : forall A B : Prop, (A \/ ~ A) -> (B \/ ~ B) -> (A \/ B) \/ ~ (A \/ B).
Proof. clear. intros A B HA HB. tauto. Qed.
Lemma AGREE0 : forall a, 0 <= a < 2 ^ 64 -> ~ XC a -> ~ (sp0 - ASTACK <= a < sp0) -> forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ra NX NS v Hv. unfold rd0, rd', aview, mbyte, mrestrict in *.
assert (Hm : mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ apply MEQF; rewrite unsigned_lit_small by exact Ra.
- intros Hw. unfold WIN, WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [exact (NS Hw) | apply NX; left; exact Hw | apply NX; right; left; exact Hw |].
destruct Hw as [Hw|[Hw|Hw]]; apply NX; unfold XC; [right; right; left; exact Hw | do 3 right; left; exact Hw | do 4 right; left; exact Hw].
- intros [Hg Hq]. apply NX. do 6 right. exact (conj Hg Hq).
- intros [Hs|Hd]; [apply NS; clear - Hs; unfold DEP_STK, ASTACK in *; zlia | apply NX; do 5 right; left; exact Hd]. }
rewrite Hm. destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [unfold seg_rom in Hv; rewrite (memory_read1_hidden tfibsegs (w_H W) (w_Hoff W) _ Eh) in Hv; discriminate Hv|].
rewrite (MONf _ Eh). exact Hv.
Qed.
Lemma AGREED : forall a, 0 <= a < 2 ^ 64 -> DZONE a -> rd' a = rdD a.
Proof. clearP. intros a Ra Hd. unfold rd', rdD. apply aview_same. apply EQD. rewrite unsigned_lit_small by exact Ra. exact Hd. Qed.
Lemma AGX : forall a, aowned B ly S a -> ~ XC a -> forall v, rd0 a = Some v -> rd' a = Some v.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem0 md0 a HAR Ho) as Ra. ceil.
pose proof (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR) as NS. destruct Hsp as (S1 & S2 & S3 & S4).
apply AGREE0; [clear - Ra; zlia | exact Hx |]. intros Hs. apply NS; [|exact Ho]. clear - Hs S1 S3. unfold sp0 in *. zlia.
Qed.
Lemma XC_where : forall a, XC a ->
(T <= a < T + kThreadObjSize /\ WINT a) \/ (0x10000 <= a < 0x5fa000 /\ (WINI a \/ 0x176e88 <= a < 0x5c7610)) \/ (Qb <= a < Qb + kPtrArrayResv) \/
(mb <= a < mb + MSv) \/ (2148234240 <= a < kHighShadowEnd /\ SMv <= a < SMv + MSv / 8) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Proof.
intros a Hx. pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof Hidx as HI. pose proof Hres as [HRS _].
pose proof BSLv_range as HB. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _).
unfold XC in Hx. destruct Hx as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[_ Hw]]]]]]].
- left. split; [|exact Hw]. unfold WINT, t_unwinding, kThreadObjSize in *. clear - Hw MZ. zlia.
- right; left. split; [|left; exact Hw]. unfold WINI in Hw. clear - Hw HB MZ. unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
- do 2 right; left. unfold QSv in Hw. clear - Hw HI HRS MZ. unfold kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
- do 3 right; left. exact Hw.
- do 4 right; left. split; [| exact Hw]. pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 map_facts))))))))))))))) as SMA.
rewrite SMA in Hw, SM2. unfold shadow_addr, SHADOW_OFF in *. clear - Hw M1 SM2 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in M1. assert (DD : 783360 <= mb / 8) by (apply Z.div_le_lower_bound; zlia). zlia.
- unfold DZONE in Hw. destruct Hw as [Hw|[Hw|Hw]]; [right; left; split; [clear - Hw MZ; zlia | right; exact Hw] | do 5 right; left; exact Hw | do 6 right; exact Hw].
- do 2 right; left. unfold QR in Hw. clear - Hw HI HRS F9 MZ. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. try unfold Qb in *. zlia.
Qed.
Lemma Z_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof blocks_facts as (NBhi & SBhi & _). destruct Hmap_apart as (_ & _ & MP3 & _). pose proof HCX as (CP & CT & QT & CQ).
pose proof (pairwise_ij _ _ 0 0 _ _ (lo_disj ly LY) eq_refl eq_refl) as PQ. pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT.
pose proof (pairwise_ij _ _ 0 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as PNB. pose proof (pairwise_ij _ _ 0 4 _ _ (lo_disj ly LY) eq_refl eq_refl) as PSB.
unfold zdisjoint in MP3, PQ, PT, PNB, PSB. cbn [fst snd] in MP3, PQ, PT, PNB, PSB.
clear - Ha Hx F3 F6 MP3 PQ PT PNB PSB. numconst. unfold kPtrArrayResv, kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
unfold WINT, WINI, DZONE in *. decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_ext : forall (i : nat) e a, nth_error (owned_extents ly) i = Some e -> (i = 3 \/ i = 6 \/ i = 7)%nat -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros i e a He Hi Ha Hx. apply XC_where in Hx. pose proof (lo_app ly LY) as HIG. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ i _ HIG He) as IH. cbv beta in IH.
assert (He2 : nth_error (static_extents ly) i = Some e) by (unfold static_extents; rewrite nth_error_app1 by (cbn; zlia); exact He).
pose proof (pairwise_ij _ _ i (9 - i - 1) _ _ HD He2 ltac:(destruct Hi as [-> |[-> | ->]]; reflexivity)) as D9.
assert (SZ : 0 <= snd e) by (destruct Hi as [-> |[-> | ->]]; injection He as <-; cbn; unfold kFakeStackSize; zlia).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ IH ltac:(destruct e; exact D9)) as Z3.
pose proof (zone3_apart_img _ _ a Z3) as EI. pose proof (zone3_apart_hsh _ _ a Z3) as EH. unfold zone3 in Z3. destruct Z3 as (E4096 & ECEIL & _).
unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in EI, EH.
assert (D : forall j e', nth_error (owned_extents ly) j = Some e' -> (j = 1 \/ j = 2 \/ j = 4 \/ j = 5)%nat -> zdisjoint e e').
{ intros j e' He' Hj. unfold static_extents in HD.
assert (HD' : pairwise zdisjoint (owned_extents ly)) by (apply (pairwise_app_inv zdisjoint (owned_extents ly) [_; _]) in HD; tauto).
destruct (Nat.lt_ge_cases i j) as [L|L].
- replace j with (i + Datatypes.S (j - i - 1))%nat in He' by zlia. exact (pairwise_ij _ _ _ _ _ _ HD' He He').
- apply zdisjoint_sym. assert (j <> i) by (intros ->; zlia). replace i with (j + Datatypes.S (i - j - 1))%nat in He by zlia. exact (pairwise_ij _ _ _ _ _ _ HD' He' He). }
pose proof (D 1%nat _ eq_refl ltac:(zlia)) as D1. pose proof (D 2%nat _ eq_refl ltac:(zlia)) as D2.
pose proof (D 4%nat _ eq_refl ltac:(zlia)) as D4. pose proof (D 5%nat _ eq_refl ltac:(zlia)) as D5.
unfold zdisjoint in D1, D2, D4, D5. cbn [fst snd] in D1, D2, D4, D5.
assert (DM : zdisjoint (mb, MSv) e).
{ apply (proj1 (Forall_forall _ _) GAPART e). apply in_app_iff. left. unfold static_extents. apply in_app_iff. left. eapply nth_error_In. exact He. }
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof blocks_facts as (NBhi & SBhi & _).
unfold zdisjoint in DM. cbn [fst snd] in DM.
clear - EI EH E4096 ECEIL Ha Hx D1 D2 D4 D5 DM M1 SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, WINT, WINI, DZONE in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_sec : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XC a.
Proof.
intros e a He Ha Hx. apply XC_where in Hx. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e He) as (_ & HIA & _).
assert (D : forall e', In e' (owned_extents ly) -> zdisjoint e e').
{ intros e' He'. exact (pairwise_In zdisjoint _ e e' (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(unfold static_extents; apply in_app_iff; left; exact He')). }
pose proof (D (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn; tauto)) as DQ.
pose proof (D (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as DT.
pose proof (D (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as DNB.
pose proof (D (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn; tauto)) as DSB.
assert (DM : zdisjoint (mb, MSv) e).
{ apply (proj1 (Forall_forall _ _) GAPART e). apply in_app_iff. right. apply in_app_iff. right. exact He. }
pose proof (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD He ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)) as D9.
assert (SZ : 0 <= snd e) by (clear - Ha; zlia).
pose proof (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(destruct e; exact D9)) as Z3.
pose proof (zone3_apart_img _ _ a Z3) as EI. pose proof (zone3_apart_hsh _ _ a Z3) as EH. unfold zone3 in Z3. destruct Z3 as (E4096 & ECEIL & _).
unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in EI, EH.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ. pose proof blocks_facts as (NBhi & SBhi & _).
unfold zdisjoint in DQ, DT, DNB, DSB, DM. cbn [fst snd] in DQ, DT, DNB, DSB, DM.
clear - EI EH E4096 ECEIL Ha Hx DQ DT DNB DSB DM M1 SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, WINT, WINI, DZONE in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma Z_T : forall a, T <= a < T + kThreadObjSize -> ~ WINT a -> ~ XC a.
Proof.
intros a Ha Hw Hx. apply XC_where in Hx. pose proof high_facts as (F1 & F2 & _). pose proof HCX as (_ & _ & QT & _). destruct Hmap_apart as (MT & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zdisjoint in QT, MT, TNB, TSB. cbn [fst snd] in QT, MT, TNB, TSB.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in TI, TH.
clear - Ha Hw Hx TI TH QT MT TNB TSB SM2 MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | exact (Hw ltac:(assumption))].
Qed.
Lemma Z_img : forall a, 0x10000 <= a < 0x5fa000 -> ~ WINI a -> ~ (0x176e88 <= a < 0x5c7610) -> ~ XC a.
Proof.
intros a Ha Hw Hd Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
clear - Ha Hw Hd Hx TI QI NI BI MI SM1 MZ. numconst. unfold kHighShadowBeg in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | exact (Hw ltac:(assumption)) | exact (Hd ltac:(assumption))].
Qed.
Lemma Z_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> ~ (QSv <= a < QSv + 8) -> ~ (grow = true /\ QR a) -> ~ XC a.
Proof.
intros a Ha Hs Hq Hx. pose proof Hx as Hx0. apply XC_where in Hx. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof HCX as (_ & _ & QT & _). destruct Hmap_apart as (_ & _ & _ & MQ & _).
pose proof blocks_facts as (NBhi & SBhi & _ & _ & QNB & QSB & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof map_zoneN as MZ.
unfold zdisjoint in QT, MQ, QNB, QSB. cbn [fst snd] in QT, MQ, QNB, QSB.
pose proof BSLv_range as HB.
unfold XC in Hx0. destruct Hx0 as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]]; [| | exact (Hs Hw) | | | | exact (Hq Hw)];
pose proof (zone3_apart_img _ _ a F9) as QI; pose proof (zone3_apart_hsh _ _ a F9) as QH; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kPtrArrayResv in QI, QH;
clear - Ha Hw QI QH F10 QT MQ QNB QSB SM2 HB MZ; unfold WINT, WINI, DZONE in *;
numconst; unfold kHighShadowBeg, kHighShadowEnd, kPtrArrayResv, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *; try unfold T in *; try unfold Qb in *; zlia.
Qed.
Lemma Z_band : forall a, in_band_rw a -> ~ (SMv <= a < SMv + MSv / 8) -> ~ XC a.
Proof.
intros a Ha Hs Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
unfold in_band_rw in Ha. clear - Ha Hs Hx TH QH NH BH MH MZ. numconst. unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; first [zlia | exact (Hs ltac:(split; assumption))].
Qed.
Lemma WINI_dec : forall a, WINI a \/ ~ WINI a.
Proof. clearP. intros a. unfold WINI. repeat (apply or_dec; [apply zr_dec|]); apply zr_dec. Qed.
Lemma PRES_MONO : forall u, 0 <= u < 2 ^ 64 -> ~ WINI u -> apresent (w_H W) mem0 u -> apresent (w_H Wz) mem' u.
Proof.
{ intros u Ru NWI Hp.
assert (HpW : apresent (w_H Wz) mem0 u) by (destruct Hp as [Hh Hb]; split; [exact (MONf _ Hh) | exact Hb]).
destruct (zr_dec 0x176e88 0x5c7610 u) as [D1|D1].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact HpW]]; [rewrite unsigned_lit_small by exact Ru|]; unfold DZONE; left; exact D1. }
destruct (zr_dec (ly_NB ly) (ly_NB ly + kNodesBlockSize) u) as [D2|D2].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact HpW]]; [rewrite unsigned_lit_small by exact Ru|]; unfold DZONE; right; left; exact D2. }
destruct (zr_dec (ly_SB ly) (ly_SB ly + kStoreBlockSize) u) as [D3|D3].
{ eapply apresent_same; [apply EQD | apply PRD; [|exact HpW]]; [rewrite unsigned_lit_small by exact Ru|]; unfold DZONE; right; right; exact D3. }
destruct (zr_dec (sp0 - ASTACK) sp0 u) as [D4|D4]; [apply PRS; exact D4|].
destruct (zr_dec mb (mb + MSv) u) as [D5|D5]; [apply PRmap; exact D5|].
destruct (zr_dec SMv (SMv + MSv / 8) u) as [D6|D6]; [apply PRsh; exact D6|].
destruct (zr_dec QSv (QSv + 8) u) as [D7|D7]; [apply PRW; right; exact D7|].
assert (DW : WINT u \/ ~ WINT u) by (clear; unfold WINT; zlia).
destruct DW as [D8|D8]; [apply PRW; left; exact D8|].
assert (D8' : ~ (WINT u \/ WINI u)) by (clear - D8 NWI; tauto). clear D8. rename D8' into D8.
destruct grow eqn:Eg.
- destruct (zr_dec (Qb + 8 * res) (Qb + 8 * res + 8 * kPtrArrayEntriesPerCommit) u) as [D9|D9].
+ destruct (Z_lt_le_dec u (Qb + kPtrArrayResv)) as [D10|D10]; [apply (PRq eq_refl); unfold QR; exact (conj D9 D10)|].
eapply apresent_same; [|exact HpW]. apply MEQF; rewrite unsigned_lit_small by exact Ru.
* unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
* intros [_ [_ Hq]]. clear - Hq D10. zlia.
* unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [zlia | tauto].
+ eapply apresent_same; [|exact HpW]. apply MEQF; rewrite unsigned_lit_small by exact Ru.
* unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
* intros [_ [Hq _]]. exact (D9 Hq).
* unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [zlia | tauto].
- eapply apresent_same; [|exact HpW]. apply MEQF; rewrite unsigned_lit_small by exact Ru.
+ unfold WIN, WINM. clear - D4 D5 D6 D7 D8. tauto.
+ intros [E _]. discriminate E.
+ unfold DX, DZONE. clear - D1 D2 D3 D4. unfold DEP_STK, ASTACK in *. intros [Hs|Hd]; [zlia | tauto]. }
Qed.
Lemma VIS_MONO : forall a, rd0 a <> None -> rd' a <> None.
Proof.
intros a0 HV0.
set (a := bv_unsigned (Z_to_bv 64 a0)).
assert (Ra : 0 <= a < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
assert (AV : forall (Hh : word -> bool) m, aview tfibsegs Hh m a0 = aview tfibsegs Hh m a) by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
unfold rd0 in HV0. rewrite AV in HV0. unfold rd'. rewrite AV. clearbody a. clear Ex AV a0. rename HV0 into HV.
destruct (WINI_dec a) as [HWI|NWI]; [exact (VISW a HWI)|].
unfold rd', rd0, aview, mbyte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [r|] eqn:ER.
- destruct (mrestrict (w_H Wz) mem' (Z_to_bv 64 a)); cbn; discriminate.
- assert (Hp : apresent (w_H W) mem0 a).
{ unfold mrestrict in HV. unfold apresent. destruct (w_H W (Z_to_bv 64 a)); [exfalso; apply HV; reflexivity|].
split; [reflexivity|]. destruct (mem0 (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply HV; reflexivity]. }
destruct (PRES_MONO a Ra NWI Hp) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma apresent_vis : forall a, apresent (w_H Wz) mem' a -> rd' a <> None.
Proof. clearP. intros a [Hh [b Hb]]. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.
Lemma ZKEEP : forall g, g mod 8 = 0 -> in_app g 8 -> (g + 8 <= mb \/ mb + MSv <= g) ->
mem' (w64 (shadow_addr g)) = mem0 (w64 (shadow_addr g)).
Proof.
intros g Hg Happ HM. pose proof (shadow_addr_band_rw g Happ) as SBg. unfold in_band_rw in SBg. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hidx as HI. pose proof Hres as [HRS _].
assert (NS : ~ (SMv <= shadow_addr g < SMv + MSv / 8)).
{ rewrite SMA. unfold shadow_addr, SHADOW_OFF. apply Z.mod_divide in Hg as [q Hq]; [|zlia]. apply Z.mod_divide in M3 as [p Hp]; [|zlia].
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _). apply Z.mod_divide in Z9 as [u Hu]; [|zlia].
rewrite Hq, Hp, Hu in *. replace (q * 8 / 8) with q by (symmetry; apply Z.div_mul; zlia).
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite Z.div_mul by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z.div_mul by zlia.
clear - HM MZ. zlia. }
unfold w64. apply MEQF; rewrite unsigned_lit_small by (clear - SBg MZ; unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; zlia).
- intros HW. unfold WIN, WINT, WINI, WINM in HW. pose proof BSLv_range as HB.
pose proof (zone3_apart_hsh _ _ (shadow_addr g) F1) as TH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) F9) as QH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) (mzone_zone3 _ _ (proj2 Hmap))) as MH.
clear - HW NS SBg TH QH MH M1 S1 T7 HB HI HRS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold QSv in *. try unfold sp0 in *. try unfold T in *. try unfold Qb in *. zlia.
- intros [_ Hq]. unfold QR in Hq. pose proof (zone3_apart_hsh _ _ (shadow_addr g) F9) as QH. clear - Hq SBg QH HI HRS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- intros [Hs|Hd]; [clear - Hs SBg S1 T7 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, DEP_STK, ASTACK in *; try unfold sp0 in *; zlia|].
unfold DZONE in Hd. pose proof (zone3_apart_hsh _ _ (shadow_addr g) NBhi) as NH. pose proof (zone3_apart_hsh _ _ (shadow_addr g) SBhi) as BH.
clear - Hd SBg NH BH MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. zlia.
Qed.
Lemma BANDKEEP : forall a, in_band_rw a -> mem0 (w64 a) <> None -> mem' (w64 a) <> None.
Proof.
intros a Ha Hm0. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; zlia).
destruct (zr_dec SMv (SMv + MSv / 8) a) as [D|D].
{ destruct (PRsh a D) as [_ [b Hb]]. unfold w64. rewrite Hb. discriminate. }
pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _). pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof Hidx as HI. pose proof Hres as [HRS _]. pose proof BSLv_range as HB.
unfold w64. rewrite MEQF; [exact Hm0 | | |]; rewrite ?unsigned_lit_small by exact Ra.
- intros HW. unfold WIN, WINT, WINI, WINM in HW. unfold in_band_rw in Ha.
pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH.
clear - HW D Ha TH QH MH M1 S1 T7 HB HI HRS MZ.
unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, ASTACK, t_unwinding, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold QSv in *. try unfold sp0 in *. try unfold T in *. try unfold Qb in *. zlia.
- intros [_ Hq]. unfold QR in Hq. unfold in_band_rw in Ha. pose proof (zone3_apart_hsh _ _ a F9) as QH. clear - Hq Ha QH HI HRS MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kPtrArrayResv in *. try unfold Qb in *. zlia.
- unfold in_band_rw in Ha. intros [Hs|Hd]; [clear - Hs Ha S1 T7 MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, DEP_STK, ASTACK in *; try unfold sp0 in *; zlia|].
unfold DZONE in Hd. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_hsh _ _ a SBhi) as BH.
clear - Hd Ha NH BH MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in *. zlia.
Qed.
Lemma cell_holds_ext1 : forall (rd1 rd2 : reader) c,
(forall k v, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd1 (aeval B ly (c_at c) + k) = Some v -> rd2 (aeval B ly (c_at c) + k) = Some v) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c.
Proof.
clearP. intros rd1 rd2 c Hx Hc. unfold cell_holds in *. destruct (c_val c) as [e|m v].
- intros k Hk. apply Hx; [zlia | exact (Hc k Hk)].
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). apply Hx; [zlia|]. rewrite Z.add_0_r. exact Hb.
Qed.
Definition loc_ok (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ~ XC a.
Lemma keep_cells : forall lst lo len, loc_ok lo len -> incl lst (acells B ly S) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst lo len LOC INC RNG. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) RNG c Hc) as [R1 R2]. cbv beta in R1, R2.
apply (cell_holds_ext1 rd0); [| exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c (INC c Hc))].
intros k v Hk Hv. apply AGX; [| | exact Hv].
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c (INC c Hc) k Hk).
- apply LOC. zlia.
Qed.
Lemma keep_cell : forall c lo len, loc_ok lo len -> In c (acells B ly S) ->
lo <= aeval B ly (c_at c) -> aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len -> cell_holds B ly rd' c.
Proof.
intros c lo len LOC Hc R1 R2. exact (proj1 (Forall_forall _ _) (keep_cells [c] lo len LOC ltac:(intros x [<-|[]]; exact Hc) ltac:(constructor; [split; assumption | constructor])) c (or_introl eq_refl)).
Qed.
Lemma keep_cellX : forall c, In c (acells B ly S) -> (forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> ~ XC (aeval B ly (c_at c) + k)) -> cell_holds B ly rd' c.
Proof.
intros c Hc NX. apply (cell_holds_ext1 rd0); [| exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) c Hc)].
intros k v Hk Hv. apply AGX; [exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) c Hc k Hk) | exact (NX k Hk) | exact Hv].
Qed.
Lemma SF_parts :
(forall c, reg SF c = reg S c) /\ st_cache_inited SF = st_cache_inited S /\ (forall c, cache SF c = cache S c) /\
frames SF = frames S /\ st_qthread SF = st_qthread S /\ st_qglobal SF = st_qglobal S /\ st_fs SF = st_fs S /\
st_internal_inited SF = st_internal_inited S /\ st_sec_arr SF = st_sec_arr S ++ [rS S] /\
st_sec_reserved SF = (if grow then res + kPtrArrayEntriesPerCommit else res) /\ st_depot SF = st_depot (depot_after z tr S) /\
st_chunks SF = st_chunks S ++ [KSc] /\ st_secs SF = st_secs S ++ [mkSec MSv NDv true] /\ st_nev SF = st_nev S + 1 /\ st_regions SF = st_regions S.
Proof.
unfold SF, SFS, sfinal, resF, depF, KSc, reg, cache, frames. cbn. rewrite <- Hres_def.
repeat split; try reflexivity. unfold depot_after. destruct (z =? 0); reflexivity.
Qed.
Lemma rS_not_in_arr : ~ In (rS S) (st_sec_arr S).
Proof.
intros Hin. pose proof (proj1 (ws_arr_live _ (wf_secondary _ _ _ _ _ WF) (rS S)) Hin) as (sm & Hsm & _).
apply nth_error_lt in Hsm. unfold rS in Hsm. zlia.
Qed.
Lemma len_arr : Z.of_nat (length (st_sec_arr S)) = idx.
Proof. rewrite Hidx_def. reflexivity. Qed.
Ltac fcons' := apply Forall_cons; [cbn; zlia|].
Lemma val_mem_at : forall a a' (w : nat) x, a = a' -> val_mem tfibsegs m' a' w x -> val_mem tfibsegs m' a w x.
Proof. clearP. intros a a' w x -> H. exact H. Qed.
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (Rreg & _). apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (region_cells SF c) with (region_cells S c) by (unfold region_cells; rewrite Rreg; reflexivity).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & _).
apply (keep_cells _ (ly_space ly + kRegionInfoOff) 4096).
- intros a Ha. apply Z_prim; clear - Ha F3 F4 F5; unfold kRegionInfoOff in *; numconst; zlia.
- intros x Hx. unfold acells. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; zlia | exact Hx].
- unfold region_cells, kRegionInfoOff. destruct (rg_mapped_user (reg S c) =? 0); repeat fcons'; apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells SF) (zseq 1 31)).
Proof.
pose proof SF_parts as (_ & Rinit & Rcache & _). apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc.
replace (cache_cells SF c) with (cache_cells S c) by (unfold cache_cells; rewrite Rinit, (Rcache c); reflexivity).
apply (keep_cells _ (T + t_cache + 80 * c) 80).
- intros a Ha. apply Z_T; unfold WINT in *; unfold T in *; clear - Ha Hc; numconst; zlia.
- intros x Hx. unfold acells. apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists c. split; [apply In_zseq; zlia | exact Hx].
- unfold cache_cells. pose proof (wf_classes _ _ _ _ _ WF c ltac:(zlia)) as CL. pose proof (wr_cache _ _ _ _ _ _ CL) as WC.
pose proof (class_ok c ltac:(zlia)) as (_ & _ & _ & K4 & _). unfold T.
destruct (st_cache_inited S).
+ destruct WC as [PM PL]. unfold t_cache. repeat fcons'. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i vv] & <- & Hiv).
apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. zlia.
+ unfold t_cache. repeat fcons'. apply Forall_nil.
Qed.
Lemma cells_chunks_old : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
apply (keep_cells _ (ck_base B ly k) (ck_rz k)).
- intros a Ha. destruct (extent_zone B ly S rd0 k MA Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ apply Z_prim. clear - Ha X1 X2 G8 Q2. zlia.
+ apply (Z_sec (m, len)); [exact Hin | cbn [fst snd]; clear - Ha X1 X2 G8 Q2; unfold kPage in *; zlia].
- intros x Hx. unfold acells. do 2 (apply in_app_iff; right). apply in_app_iff; left. apply in_flat_map. exists k. split; [exact Hk | exact Hx].
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c p]; try solve [destruct GG]; cbn; zlia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
+ repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
+ destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
assert (32 <= ck_rz k). { apply Z.mod_divide in G6 as [q Hq]; [|zlia]. zlia. }
repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.max Z.of_nat Pos.of_succ_nat Pos.succ]; zlia|]). apply Forall_nil.
Qed.
Lemma cells_chunks_new : Forall (cell_holds B lyF rd') (chunk_cells KSc).
Proof.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS.
unfold chunk_cells, hdr_state. rewrite KR, KN, KST, KB. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb].
assert (EV : forall d, aeval B lyF (ASec (rS S) d) = mb + d) by (intros d; cbn [aeval aoff]; rewrite LS; reflexivity).
assert (EV2 : forall d d', aeval B lyF (aoff (ASec (rS S) d) d') = mb + d + d') by (intros d d'; cbn [aeval aoff]; rewrite LS; zlia).
assert (EV3 : forall d d' d'', aeval B lyF (aoff (aoff (ASec (rS S) d) d') d'') = mb + d + d' + d'') by (intros d d' d''; cbn [aeval aoff]; rewrite LS; zlia).
pose proof Vst as W1. pose proof Vb1 as W2. pose proof Vb2 as W3. pose proof Vn as W4. pose proof Vmag as W5. pose proof Vbk as W6. unfold Uv, Kv in W1, W2, W3, W4, W5, W6.
constructor. { apply val_mem_cell. rewrite EV2. cbn [aeval]. apply (val_mem_at _ (mb + 6144 - 16)); [zlia | exact W1]. }
constructor. { cbn [cell_holds c_at c_val c_w]. rewrite EV3. pose proof (W2 0%nat ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold m' in X.
exists 17. split; [|reflexivity]. unfold rd', aview. replace (mb + 4096 + (2048 - 16) + 1) with (mb + 6144 - 15) by zlia. rewrite X. cbn [option_map].
rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. reflexivity. }
constructor. { apply val_mem_cell. rewrite EV3. cbn [aeval]. apply (val_mem_at _ (mb + 6144 - 14)); [zlia | exact W3]. }
constructor. { apply val_mem_cell. rewrite EV3. cbn [aeval]. apply (val_mem_at _ (mb + 6144 - 12)); [zlia | exact W4]. }
constructor. { apply val_mem_cell. rewrite EV. cbn [aeval]. apply (val_mem_at _ (mb + 4096)); [zlia | exact W5]. }
constructor. { apply val_mem_cell. rewrite !EV2. apply (val_mem_at _ (mb + 4096 + 8)); [zlia |]. replace (mb + 4096 + (2048 - 16)) with (mb + 6144 - 16) by zlia. exact W6. }
apply Forall_nil.
Qed.
Lemma cells_sec_old_arr : Forall (cell_holds B ly rd') (map (fun ir => c8 (AQ (8 * Z.of_nat (fst ir))) (ASec (snd ir) 0)) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
Proof.
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
apply Forall_forall. intros c Hc. pose proof Hc as Hc0. apply in_map_iff in Hc as ([i r] & <- & Hir). pose proof Hir as Hi. apply in_combine_l in Hi. apply in_seq in Hi.
apply keep_cellX; [apply INC; unfold sec_cells; do 3 right; apply in_app_iff; left; exact Hc0|].
intros k Hk. cbn [c_at c_w c_val aeval c8 fst snd] in Hk |- *. pose proof len_arr as LA. pose proof Hres as [HRS _]. pose proof Hidx as HI.
apply Z_Q; [try unfold Qb; clear - Hk Hi LA HRS HI; unfold kPtrArrayResv, kMaxNumChunks in *; zlia | unfold QSv; clear - Hk Hi LA; try unfold Qb; zlia |].
intros [_ Hq]. unfold QR in Hq. clear - Hk Hi LA HRS Hq. try unfold Qb in *. zlia.
Qed.
Lemma cells_sec_old_hdr : Forall (cell_holds B ly rd') (flat_map (fun k => match ck_beg k with
| PSec r _ => [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k)); z8 (ASec r 16) (needed_size (ck_req k)); z8 (ASec r 24) (index_ofZ (st_sec_arr SF) r) ]
| _ => [] end) (st_chunks S)).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & _). rewrite Rarr.
assert (INC : forall x, In x (sec_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p] eqn:Eb; try apply Forall_nil. destruct GG as (_ & _ & Gbase & Gext & Gin & _).
assert (INr : In r (st_sec_arr S)) by (apply (proj2 (ws_arr_chunks _ (wf_secondary _ _ _ _ _ WF) r)); exists k; split; [exact Hk | rewrite Eb; destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; destruct GG' as (-> & _); reflexivity]).
rewrite (index_ofZ_app_old _ _ _ INr).
pose proof (secondary_geometry (ck_req k) ltac:(zlia) ltac:(destruct (chunk_facts B ly S rd0 k MA Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & GG'); rewrite Eb in GG'; tauto)) as (_ & _ & SG & _).
apply (keep_cells _ (ly_sec ly r) (sec_map_size (ck_req k))).
- intros a Ha. apply (Z_sec (ly_sec ly r, sec_map_size (ck_req k))); [exact Gin | cbn [fst snd]; exact Ha].
- intros x Hx. apply INC. unfold sec_cells. do 3 right. apply in_app_iff. right. apply in_flat_map. exists k. rewrite Eb. split; [exact Hk | exact Hx].
- unfold kPage, kSecRz in *. pose proof (req_size_bounds (ck_req k) ltac:(zlia)) as (Q1 & Q2 & Q3).
repeat (apply Forall_cons; [cbn [c_at c_w aeval c8 z8]; zlia|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B lyF rd') (sec_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _ & Rck & _). pose proof (ts_inst B TS) as EI. pose proof len_arr as LA. pose proof lyF_sec as LS.
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_eqs as (_ & _ & EQ & _).
unfold sec_cells. rewrite Rres, Rarr, Rck.
constructor. { apply val_mem_cell. cbn [aeval]. rewrite EI. exact Vres. }
constructor. { apply val_mem_cell. cbn [aeval]. rewrite EI. rewrite length_app. cbn [length]. replace (Z.of_nat (length (st_sec_arr S) + 1)) with (idx + 1) by zlia. exact Vnch. }
constructor. { apply val_mem_cell. cbn [aeval]. rewrite EI. exact Vmtx. }
apply Forall_app. split.
- rewrite length_app. cbn [length]. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir).
destruct (Nat.eq_dec i (length (st_sec_arr S))) as [->|Hne].
+   assert (Er : r = rS S).
{ replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS S])) in Hir by (rewrite length_app; reflexivity).
destruct (in_combine_seq _ _ _ _ Hir) as [E _]. rewrite Nat.sub_0_r, nth_error_app2 in E by zlia. rewrite Nat.sub_diag in E. cbn in E. injection E as <-. reflexivity. }
subst r. apply val_mem_cell. cbn [aeval fst snd]. rewrite EQ, LS, LA, Z.add_0_r. unfold QSv in Vslot. exact Vslot.
+   assert (Hold : In (i, r) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))).
{ replace (length (st_sec_arr S) + 1)%nat with (length (st_sec_arr S ++ [rS S])) in Hir by (rewrite length_app; reflexivity).
destruct (in_combine_seq _ _ _ _ Hir) as [E R]. rewrite length_app in R. cbn [length] in R. rewrite Nat.sub_0_r in E.
rewrite nth_error_app1 in E by zlia. apply combine_seq_in; [rewrite Nat.sub_0_r; exact E | zlia]. }
apply (cell_holds_le B ly lyF _ lyF_le rd'); [| exact (proj1 (Forall_forall _ _) cells_sec_old_arr _ ltac:(apply in_map_iff; exists (i, r); split; [reflexivity | exact Hold]))].
split; cbn; [exact I|]. apply in_combine_r in Hold.
pose proof (proj1 (ws_arr_live _ (wf_secondary _ _ _ _ _ WF) r) Hold) as (sm & Hsm & _). eapply nth_error_lt. exact Hsm.
- rewrite flat_map_app. apply Forall_app. split.
+ apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [| exact cells_sec_old_hdr].
apply Forall_flat_map'. intros k Hk. pose proof (AFib_w.chunk_lt S _ _ _ _ WF k Hk) as LT.
destruct (ck_beg k) as [|o|r o|c' p]; try apply Forall_nil. repeat (apply Forall_cons; [split; cbn; first [exact LT | exact I]|]). apply Forall_nil.
+ cbn [flat_map app]. rewrite KB. rewrite app_nil_r. rewrite KQ, ND, MS. rewrite (index_ofZ_app_new _ _ rS_not_in_arr), LA.
assert (EV : forall d, aeval B lyF (ASec (rS S) d) = mb + d) by (intros d; cbn [aeval aoff]; rewrite LS; reflexivity).
constructor. { apply val_mem_cell. rewrite !EV, Z.add_0_r. exact Vh0. }
constructor. { apply val_mem_cell. rewrite EV. cbn [aeval]. exact Vh8. }
constructor. { apply val_mem_cell. rewrite EV. cbn [aeval]. exact Vh16. }
constructor. { apply val_mem_cell. rewrite EV. cbn [aeval]. exact Vh24. }
apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wf_quarantine _ _ _ _ _ WF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (LOC : loc_ok (ly_space ly + b_self b) kBatchBytes).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; zlia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wr_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_user_bound (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; zlia)) as MB.
pose proof (region_in_prim ly kBatchClass LY ltac:(unfold kBatchClass; zlia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; zlia).
intros a Ha. apply Z_prim. clear - Ha X1 X2 AL MB R1 R2 BX. unfold kBatchBytes, kUserMapSize, EV_MAX in *. zlia. }
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOC); [apply INC; right; right; left; reflexivity | cbn; zlia | cbn; unfold kBatchBytes; zlia]|].
apply Forall_app. split.
- apply (keep_cells _ _ _ LOC).
+ intros y Hy. apply INC. do 3 right. apply in_app_iff. left. exact Hy.
+ apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
cbn. unfold kBatchBytes. zlia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma Z_quar : forall a, TFIB_INST + o_quar <= a < 0x176e88 -> ~ XC a.
Proof.
intros a Ha. pose proof BSLv_range as HB. apply Z_img; [clear - Ha; unfold TFIB_INST, o_quar in *; zlia | | clear - Ha; zlia].
unfold WINI. clear - Ha HB. unfold TFIB_INST, o_quar, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. zlia.
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & Rqt & Rqg & _).
replace (quar_cells SF) with (quar_cells S) by (unfold quar_cells; rewrite Rqt, Rqg; reflexivity).
assert (INC : forall x, In x (quar_cells S) -> In x (acells B ly S)) by (intros x Hx; unfold acells; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hx).
pose proof (ts_inst B TS) as EI.
assert (LOCI : loc_ok (TFIB_INST + o_quar) 400) by (intros a Ha; apply Z_quar; clear - Ha; unfold TFIB_INST, o_quar in *; zlia).
assert (LOCT : loc_ok (T + t_qc) 32) by (intros a Ha; apply Z_T; unfold WINT, t_qc, t_unwinding, kThreadObjSize in *; unfold T in *; clear - Ha; zlia).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, o_quar, t_qc in *.
apply Forall_cons; [apply (keep_cell _ _ _ LOCI); [apply INC; left; reflexivity | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia]|].
apply Forall_cons; [apply (keep_cell _ _ _ LOCI); [apply INC; right; left; reflexivity | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia]|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCT); [apply INC; right; right; apply in_app_iff; left; cbn; tauto | cbn; unfold T; zlia | cbn; unfold T; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [apply (keep_cell _ _ _ LOCI); [apply INC; right; right; apply in_app_iff; right; cbn; tauto | cbn; rewrite EI; zlia | cbn; rewrite EI; zlia]|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & Rfs & _).
replace (fs_cells SF) with (fs_cells S) by (unfold fs_cells; rewrite Rfs; reflexivity).
apply (keep_cells _ (ly_F ly) kFakeStackSize).
- intros a Ha. apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]; exact Ha].
- intros x Hx. unfold acells. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold fs_cells, kFakeStackSize. fcons'. fcons'. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih).
apply in_combine_l in Hih. apply in_seq in Hih. cbn. zlia.
Qed.
Lemma DZONE64 : forall a, DZONE a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof blocks_facts as (NBhi & SBhi & _). unfold DZONE in Ha.
clear - Ha NBhi SBhi. numconst. zlia.
Qed.
Lemma depot_final : depot_mem_ok B ly (depot_after z tr S) rd'.
Proof.
apply (depot_mem_ok_agree _ rdD).
- pose proof (wf_depot _ _ _ _ _ WF) as [ND INCL]. pose proof (depot_ids_bound S ND INCL). unfold depot_after. destruct (z =? 0); [zlia|].
unfold depot_ids in *. cbn. rewrite length_app. cbn. zlia.
- intros a Ha. apply AGREED; [exact (DZONE64 a Ha) | exact Ha].
- exact DEPD.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
replace (depot_cells ly SF) with (depot_cells ly (depot_after z tr S)) by (unfold depot_cells, depot_ids, depot_frames; rewrite Rdep; reflexivity).
exact (proj1 depot_final).
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B SF).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & Rii & _).
replace (ialloc_cells B SF) with (ialloc_cells B S) by (unfold ialloc_cells; rewrite Rii; reflexivity).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3.
apply (keep_cells _ (TFIB_INST + o_quar) (0x176e88 - TFIB_INST - o_quar)).
- intros a Ha. apply Z_quar. zlia.
- intros x Hx. unfold acells. do 7 (apply in_app_iff; right). apply in_app_iff. left. exact Hx.
- unfold ialloc_cells. rewrite E1, E2, E3. unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_INST, o_quar.
repeat (apply Forall_cons; [cbn; rewrite ?E1, ?E3; unfold TFIB_IAL_LO, TFIB_IAL_FLAG; zlia|]). apply Forall_nil.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof. unfold thread_cells. constructor; [|apply Forall_nil]. apply val_mem_cell. cbn [aeval]. exact Vunw. Qed.
Lemma cells_final : Forall (cell_holds B lyF rd') (acells B lyF SF).
Proof.
pose proof (AFib_w.acells_lt B ly S _ _ _ _ WF) as LT. unfold acells in LT |- *.
pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E13 & _).
assert (LIFT : forall l, incl l (flat_map (region_cells S) (zseq 1 31) ++ flat_map (cache_cells S) (zseq 1 31) ++ flat_map chunk_cells (st_chunks S) ++ sec_cells S ++
quar_cells S ++ fs_cells S ++ depot_cells ly S ++ ialloc_cells B S ++ thread_cells) ->
Forall (cell_holds B ly rd') l -> Forall (cell_holds B lyF rd') l).
{ intros l INC H. apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [exact (incl_Forall INC LT) | exact H]. }
pose proof SF_parts as (Rreg & Rinit & Rcache & _ & Rqt & Rqg & Rfs & Rii & _ & _ & Rdep & Rck & _).
apply Forall_app; split.
{ apply LIFT; [| exact cells_regions]. intros x Hx. apply in_app_iff. left. apply in_flat_map in Hx as (c & Hc & Hx). apply in_flat_map. exists c.
unfold region_cells in *. rewrite Rreg in Hx. exact (conj Hc Hx). }
apply Forall_app; split.
{ apply LIFT; [| exact cells_caches]. intros x Hx. apply in_app_iff; right. apply in_app_iff; left. apply in_flat_map in Hx as (c & Hc & Hx). apply in_flat_map. exists c.
unfold cache_cells in *. rewrite Rinit, (Rcache c) in Hx. exact (conj Hc Hx). }
apply Forall_app; split.
{ rewrite Rck, flat_map_app. apply Forall_app; split.
- apply LIFT; [| exact cells_chunks_old]. intros x Hx. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. exact cells_chunks_new. }
apply Forall_app; split; [exact cells_sec|].
apply Forall_app; split.
{ apply LIFT; [| exact cells_quar]. intros x Hx. do 4 (apply in_app_iff; right). apply in_app_iff; left. unfold quar_cells in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply Forall_app; split.
{ apply LIFT; [| exact cells_fs]. intros x Hx. do 5 (apply in_app_iff; right). apply in_app_iff; left. unfold fs_cells in *. rewrite Rfs in Hx. exact Hx. }
apply Forall_app; split.
{
replace (depot_cells lyF SF) with (depot_cells ly SF) by (unfold depot_cells, depot_frames, depot_traces; rewrite E13; reflexivity).
apply (Forall_cell_holds_le B ly lyF _ lyF_le rd'); [| exact cells_depot]. unfold depot_cells. repeat (apply Forall_cons; [split; cbn; exact I|]). apply Forall_nil. }
apply Forall_app; split.
{ apply LIFT; [| exact cells_ialloc]. intros x Hx. do 7 (apply in_app_iff; right). apply in_app_iff; left. unfold ialloc_cells in *. rewrite Rii in Hx. exact Hx. }
apply LIFT; [| exact cells_thread]. intros x Hx. do 8 (apply in_app_iff; right). exact Hx.
Qed.
Lemma cell_holds_agree3 : forall (rd1 rd2 rd3 : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
(forall v, rd1 (aeval B ly (c_at c) + k) = Some v -> rd3 (aeval B ly (c_at c) + k) = Some v) \/ rd3 (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd3 c.
Proof.
clearP. intros rd1 rd2 rd3 c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(zlia)) as [E|E]; [exact (E _ (H1 k Hk)) | rewrite E; exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(zlia)) as [E|E]; rewrite Z.add_0_r in E; [exists b1; split; [exact (E _ Hb1) | exact Hm1] | exists b2; rewrite E; tauto].
Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const B ly S rd0 MA) c Hc) as HOLD.
pose proof (proj1 (Forall_forall _ _) CSTD c Hc) as HOLDD.
pose proof (const_cells_CZ c) as CCZ. destruct (padb c) eqn:Ep.
-
pose proof Hc as Hc'. rewrite (ts_const B TS ly) in Hc'. unfold Tfib_const in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
{ exfalso. revert Ep Hc'. clear. intros Ep Hc'. unfold Tfib_const_sym in Hc'. cbn [In] in Hc'.
repeat match type of Hc' with _ \/ _ => destruct Hc' as [<-|Hc']; [discriminate Ep|] | False => destruct Hc' end. }
pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => negb (padb c) || match c_val c with AV (ANum 0) => true | _ => false end) (Tfib_const_abs ++ Tfib_const_shadow) = true) c Hc') as CK.
cbn beta in CK. rewrite Ep in CK. cbn [negb orb] in CK.
unfold padb in Ep. unfold cell_holds. destruct (c_at c) eqn:Ea; try discriminate Ep. cbn [aeval] in CCZ |- *.
destruct (c_val c) as [e|mk vv]; [|discriminate CK]. destruct e; try discriminate CK.
lazymatch goal with |- context [aeval _ _ (ANum ?zz)] => destruct zz; try discriminate CK end.
intros k Hk. cbn [aeval]. pose proof (CCZ (Z.of_nat k) Hc ltac:(zlia)) as Pk. unfold MPAD in Pk.
lazymatch goal with |- _ (?a + Z.of_nat k) = _ =>
replace (a + Z.of_nat k) with (TFIB_INST + o_sec_mutex + (a + Z.of_nat k - (TFIB_INST + o_sec_mutex))) by zlia end.
rewrite Vpad by zlia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; zlia). rewrite Z.shiftr_0_l. reflexivity.
-
apply (cell_holds_agree3 rd0 rdD); [| exact HOLD | exact HOLDD].
assert (HmapD : zdisjoint (mb, MSv) (ly_D ly, 4096)).
{ apply (proj1 (Forall_forall _ _) GAPART). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto. }
intros k Hk. pose proof (CZ_untouched HmapD _ (CCZ k Hc Hk)) as (Ra & N1 & N2 & N3 & N4 & N5).
destruct (zr_dec 0x176e88 0x5c7610 (aeval B ly (c_at c) + k)) as [D|D].
+ right. apply AGREED; [exact Ra | unfold DZONE; left; exact D].
+ left. apply AGREE0; [exact Ra | | intros Hs; apply N1; unfold WIN; left; exact Hs].
intros HX. unfold XC in HX. unfold WIN, WINM in N1. unfold DZONE in HX. clear - HX N1 N2 N4 N5 D. tauto.
Qed.
Lemma CONSTlt : forall nn, Forall (AFib_w.cell_lt nn) (as_const B ly).
Proof.
intros nn. rewrite (ts_const B TS ly). clear. unfold Tfib_const, Tfib_const_sym, Tfib_const_abs, Tfib_const_shadow. cbn [app].
repeat (apply Forall_cons; [exact (conj I I)|]). apply Forall_nil.
Qed.
Lemma JUNKlt : forall nn lyx, Forall (fun r => AFib_w.asec_lt nn (fst r)) (as_junk B lyx).
Proof. intros nn lyx. apply Forall_forall. intros r Hr. destruct (ts_junk B TS lyx r Hr) as (zz & -> & _). exact I. Qed.
Lemma CONSTeq : forall ly1 ly2, as_const B ly1 = as_const B ly2.
Proof. intros ly1 ly2. rewrite !(ts_const B TS). reflexivity. Qed.
Lemma MAF : ARm B lyF S rd0.
Proof.
exact (AFib_w.ARm_layout_le B ly lyF S rd0 MA lyF_le lyF_ok (CONSTeq lyF ly) (CONSTlt _) (JUNK lyF ly) (JUNKlt _ ly)).
Qed.
Lemma const_finalF : Forall (cell_holds B lyF rd') (as_const B lyF).
Proof. rewrite (CONSTeq lyF ly). exact (Forall_cell_holds_le B ly lyF _ lyF_le rd' _ (CONSTlt _) const_final). Qed.
Lemma fa_final : fa_entries_ok lyF rd' SF.
Proof.
pose proof SF_parts as (Rreg & _). pose proof lyF_eqs as (_ & E2 & _). intros c i vv Hc Hi HV k Hk. rewrite Rreg in Hi, HV.
unfold fa_base. rewrite E2. change (ly_space ly + region_off c + kFreeArrayOffset) with (fa_base ly c).
pose proof (wf_classes _ _ _ _ _ WF c Hc) as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
apply AGX; [eapply own_fa; [exact MA | exact Hc | zlia] | | exact (am_fa _ _ _ _ MA c i vv Hc Hi HV k Hk)].
pose proof (region_in_prim ly c LY Hc) as (R1 & R2 & _).
unfold fa_base, region_base, kFreeArrayOffset, kFreeArrayMax in *.
apply Z_prim; clear - Hk Hi FL FB R1 R2 Hc; zlia.
Qed.
Lemma flags_final : fs_flags_ok lyF rd' SF.
Proof.
pose proof SF_parts as (_ & _ & _ & Rfr & _). pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). intros cid pos Hc Hp.
rewrite Rfr. unfold flag_addr. rewrite E6. pose proof (flag_off_bounds cid pos Hc Hp) as FB.
apply AGX; [unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | zlia] | | exact (am_flags _ _ _ _ MA cid pos Hc Hp)].
apply (Z_ext 3 (ly_F ly, kFakeStackSize)); [reflexivity | zlia | cbn [fst snd]].
unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. zlia.
Qed.
Lemma zero_final : Forall (range_zero B lyF rd') (ialloc_zero B).
Proof.
pose proof (am_zero _ _ _ _ MA) as Mze. pose proof (am_syms _ _ _ _ MA) as Msy.
apply Forall_forall. intros r Hr i Hi.
assert (EV : aeval B lyF (fst r) = aeval B ly (fst r)) by (unfold ialloc_zero in Hr; destruct Hr as [<-|[<-|[]]]; reflexivity). rewrite EV.
apply AGX.
- pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; zlia.
- pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2'. pose proof (ts_ial_w B TS) as E3.
apply Z_quar. unfold ialloc_zero in Hr.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2', ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_INST, o_quar in *; zlia.
- exact (proj1 (Forall_forall _ _) Mze r Hr i Hi).
Qed.
Lemma rd_byte : forall a v, 0 <= v < 256 -> w_H Wz (Z_to_bv 64 a) = false -> mem' (Z_to_bv 64 a) = Some (Z_to_bv 8 v) -> rd' a = Some v.
Proof. clearP. intros a v Hv Hh Hm. unfold rd', aview, mbyte, mrestrict. rewrite Hh, Hm. cbn [option_map]. rewrite unsigned_lit_small8 by exact Hv. reflexivity. Qed.
Lemma sh_vis : forall a, SMv <= a < SMv + MSv / 8 -> w_H Wz (Z_to_bv 64 a) = false.
Proof.
intros a Ha. pose proof (SH_hull mb) as (H1 & H2 & _). pose proof map_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
apply VISsh. rewrite unsigned_lit_small by (clear - Ha SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia). rewrite SMA in Ha. clear - Ha H1 H2 MZ. zlia.
Qed.
Lemma sh_map : forall j, shadow_addr (mb + 8 * j) = SMv + j.
Proof.
intros j. pose proof map_facts as (_ & _ & M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMA). pose proof map_zoneN as MZ. rewrite SMA. unfold shadow_addr.
apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp. replace (p * 4096 + 8 * j) with ((p * 512 + j) * 8) by zlia. replace (p * 4096) with ((p * 512) * 8) by zlia.
rewrite !Z.div_mul by zlia. zlia.
Qed.
Lemma sh_sep : forall g, g mod 8 = 0 -> (g + 8 <= mb \/ mb + MSv <= g) -> ~ (SMv <= shadow_addr g < SMv + MSv / 8).
Proof.
intros g Hg HM. pose proof map_facts as (M1 & M2 & M3 & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & _ & SMA). pose proof map_zoneN as MZ.
rewrite SMA. unfold shadow_addr, SHADOW_OFF. apply Z.mod_divide in Hg as [q Hq]; [|zlia]. apply Z.mod_divide in M3 as [p Hp]; [|zlia].
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _). apply Z.mod_divide in Z9 as [u Hu]; [|zlia].
rewrite Hq, Hp, Hu in *. replace (q * 8 / 8) with q by (symmetry; apply Z.div_mul; zlia).
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite Z.div_mul by zlia. replace (u * 4096) with ((u * 512) * 8) by zlia. rewrite Z.div_mul by zlia.
clear - HM MZ. zlia.
Qed.
Lemma in_rangesb_app : forall g l1 l2, in_rangesb g (l1 ++ l2) = (in_rangesb g l1 || in_rangesb g l2)%bool.
Proof. clear. intros g l1 l2. induction l1 as [|[lo len] t IH]; [reflexivity|]. cbn [in_rangesb app]. rewrite IH, Bool.orb_assoc. reflexivity. Qed.
Lemma ck_base_lyF : forall k, In k (st_chunks S) -> ck_base B lyF k = ck_base B ly k.
Proof. intros k Hk. unfold ck_base. apply (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le). exact (AFib_w.chunk_lt S _ _ _ _ WF k Hk). Qed.
Lemma find_chunk_at_lyF : forall g, find_chunk_at B lyF (st_chunks S) g = find_chunk_at B ly (st_chunks S) g.
Proof.
intros g. assert (H : forall l, incl l (st_chunks S) -> find_chunk_at B lyF l g = find_chunk_at B ly l g).
{ induction l as [|k t IH]; intros INC; [reflexivity|]. cbn [find_chunk_at]. rewrite (ck_base_lyF k (INC k (or_introl eq_refl))).
rewrite (IH (fun x Hx => INC x (or_intror Hx))). reflexivity. }
apply H. intros k Hk. exact Hk.
Qed.
Lemma ck_base_new : ck_base B lyF KSc = Kv.
Proof. pose proof sizes_model as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KB & _). unfold ck_base. rewrite KB. cbn [sptr_addr sptr_exp aeval]. rewrite lyF_sec. unfold Kv. reflexivity. Qed.
Lemma FPR : fa_poison_ranges lyF SF = fa_poison_ranges ly S ++ [(mb, MSv)].
Proof.
pose proof SF_parts as (Rreg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof lyF_eqs as (_ & E2 & _).
pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold fa_poison_ranges. rewrite Rck, flat_map_app, app_assoc.
pose proof (sec_extents_le ly lyF S _ _ _ _ lyF_le WF) as SE. unfold sec_extents in SE. rewrite SE.
replace (flat_map (fun k => match ck_beg k with PSec r _ => [(ly_sec lyF r, sec_map_size (ck_req k))] | _ => [] end) [KSc]) with [(mb, MSv)]
by (cbn [flat_map]; rewrite KB, KQ, MS, lyF_sec, app_nil_r; reflexivity).
f_equal; f_equal; try reflexivity;
unfold reg in Rreg |- *; unfold region_base, fa_base; rewrite ?E2; apply flat_map_ext; intros c; rewrite ?Rreg; reflexivity.
Qed.
Lemma shadow_final : shadow_ok B lyF rd' SF.
Proof.
pose proof SF_parts as (Rreg & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
pose proof map_facts as (M1 & M2 & M3 & M4 & M5 & _ & M7 & _ & _ & _ & _ & SM1 & SM2 & _ & PB & SMA). pose proof map_zoneN as MZ.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & _). pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
destruct Hmap_apart as (_ & _ & MP3 & _).
assert (C8 : ASAN_CEIL mod 8 = 0) by (pose proof (proj2 (@YG0f.ASAN_CEIL_range _)) as CM; clear - CM MZ; apply Z.mod_divide in CM as [q Hq]; [|zlia]; rewrite Hq; replace (q * 4096) with ((q * 512) * 8) by zlia; apply Z.mod_mul; zlia).
assert (M8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8.
intros g vv Hg8 HV. unfold ashadow in HV. rewrite Rck in HV.
destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
-
pose proof F0 as F0'. rewrite <- find_chunk_at_lyF in F0'. rewrite (find_chunk_at_app1 lyF _ _ _ _ F0') in HV.
pose proof F0 as F0c. apply find_chunk_at_In in F0c as [Hk0 Hg0]. rewrite (ck_base_lyF k0 Hk0) in HV.
assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0; exact HV).
pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
apply AGX; [exact (ashadow_owned B ly S rd0 g vv MA A0) | | exact (am_shadow _ _ _ _ MA g vv Hg8 A0)].
apply Z_band; [rewrite <- (Zplus_minus (ck_base B ly k0) g); apply (shadow_addr_in_band _ _ _ C1); clear - Hg0 MZ; zlia|].
apply sh_sep; [exact Hg8|]. destruct (extent_zone B ly S rd0 k0 MA Hk0) as [[X1 X2]|(m & len & Hin & X1 & X2)].
+ unfold zdisjoint in MP3. cbn [fst snd] in MP3. apply Z.mod_divide in Hg8 as [q Hq]; [|zlia]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. clear - Hg0 X1 X2 MP3 Hq Hp MZ. zlia.
+ pose proof (proj1 (Forall_forall _ _) GAPART (m, len) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply Z.mod_divide in Hg8 as [q Hq]; [|zlia]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. clear - Hg0 X1 X2 D Hq Hp MZ. unfold kPage in *. zlia.
- pose proof F0 as F0'. rewrite <- find_chunk_at_lyF in F0'. rewrite (find_chunk_at_app2 lyF _ _ _ F0') in HV. cbn [find_chunk_at] in HV.
rewrite ck_base_new, KE in HV.
destruct (andb (Kv <=? g) (g <? Kv + (MSv - 4096))) eqn:CK.
+
apply andb_prop in CK as [CK1 CK2]. apply Z.leb_le in CK1. apply Z.ltb_lt in CK2.
injection HV as HV'. cbn beta iota in HV'. rewrite ck_base_new in HV'. unfold chunk_granule in HV'. rewrite KR, KN, KST in HV'. change (2048 / 8) with 256 in HV'.
set (j := (g - Kv) / 8) in HV'.
assert (Hgj : g = mb + 8 * (512 + j)).
{ subst j. rewrite M4 in *. pose proof (Z.div_mod (g - (mb + 4096)) 8 ltac:(zlia)) as D1. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. apply Z.mod_divide in Hg8 as [q Hq]; [|zlia].
assert ((g - (mb + 4096)) mod 8 = 0) by (rewrite Hq, Hp; replace (q * 8 - (p * 4096 + 4096)) with ((q - 512 * p - 512) * 8) by zlia; apply Z.mod_mul; zlia). zlia. }
pose proof (sh_map (512 + j)) as SA. rewrite <- Hgj in SA. rewrite SA.
assert (Jhi : j < MSv / 8 - 512) by (clear - CK2 Hgj M4 DM8 M8 MZ; zlia).
assert (N8 : N8D / 8 = n / 8) by (unfold N8D; apply Z.div_mul; zlia).
assert (R8 : R8v / 8 = (n + 7) / 8) by (unfold R8v; apply Z.div_mul; zlia).
pose proof (Z.div_mod n 8 ltac:(zlia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(zlia)) as MB.
pose proof (Z.div_mod (n + 7) 8 ltac:(zlia)) as DM7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(zlia)) as MB7.
assert (VIS : w_H Wz (Z_to_bv 64 (SMv + (512 + j))) = false) by (apply sh_vis; clear - Jhi CK1 Hgj M4 MZ; zlia).
assert (R64 : 0 <= SMv + (512 + j) < 2 ^ 64) by (clear - Jhi CK1 Hgj M4 SM1 SM2 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia).
revert HV'. destruct (Z.ltb_spec j 256) as [J1|J1]; intros HV'; cbn beta iota in HV'.
*
subst vv. apply rd_byte; [unfold shHeapLeftRz; zlia | exact VIS |]. apply Vsh. rewrite unsigned_lit_small by exact R64. left. clear - J1 CK1 Hgj M4 MZ. zlia.
* revert HV'. destruct (Z.ltb_spec j (256 + n / 8)) as [J2|J2]; intros HV'; cbn beta iota in HV'.
--
subst vv. apply rd_byte; [unfold shAddressable; zlia | exact VIS |]. apply Vzs. rewrite unsigned_lit_small by exact R64. clear - J1 J2 N8 MZ. zlia.
-- revert HV'. destruct (andb (j =? 256 + n / 8) (negb (n mod 8 =? 0))) eqn:PJ; intros HV'; cbn beta iota in HV'.
++
apply andb_prop in PJ as [PJ1 PJ2]. apply Z.eqb_eq in PJ1. apply Bool.negb_true_iff in PJ2. apply Z.eqb_neq in PJ2. subst vv.
pose proof (Vpb PJ2 0%nat ltac:(zlia)) as X. rewrite Z.add_0_r in X. unfold m' in X.
assert (EP : PBv = SMv + (512 + j)) by (clear - PB PJ1 N8 MZ; zlia).
unfold rd', aview. rewrite <- EP, X. cbn [option_map]. rewrite le_byte_1_0 by zlia. rewrite unsigned_lit_small8 by zlia. reflexivity.
++
subst vv. apply rd_byte; [unfold shHeapLeftRz; zlia | exact VIS |]. apply Vsh. rewrite unsigned_lit_small by exact R64. right.
unfold UEv, SHBv. unfold SMv, SHBv in Jhi |- *. apply Z.mod_divide in M3 as [p Hp]; [|zlia].
assert (EU : (mb + 6144 + R8v) / 8 = mb / 8 + 768 + R8v / 8).
{ rewrite Hp. apply Z.mod_divide in Z2 as [r8 Hr8]; [|zlia]. rewrite Hr8. replace (p * 4096 + 6144 + r8 * 8) with ((p * 512 + 768 + r8) * 8) by zlia.
replace (p * 4096) with ((p * 512) * 8) by zlia. rewrite !Z.div_mul by zlia. zlia. }
rewrite EU, R8. apply Bool.andb_false_iff in PJ.
destruct PJ as [PJ|PJ]; [apply Z.eqb_neq in PJ | apply Bool.negb_false_iff in PJ; apply Z.eqb_eq in PJ]; clear - J1 J2 PJ Jhi DM MB DM7 MB7 MZ; split; try zlia.
all: assert (n / 8 + 1 <= j) by zlia; assert ((n + 7) / 8 <= n / 8 + 1) by zlia; zlia.
+
rewrite FPR, in_rangesb_app in HV.
destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR.
* cbn [orb] in HV. assert (A0 : ashadow B ly S g = Some vv) by (unfold ashadow; rewrite F0, IR; exact HV).
apply in_rangesb_true in IR as (lo & len & Hin & Hglo).
apply AGX; [exact (ashadow_owned B ly S rd0 g vv MA A0) | | exact (am_shadow _ _ _ _ MA g vv Hg8 A0)].
assert (GZ : (ly_prim ly <= g /\ g + 8 <= ly_prim ly + kPrimResvSize) \/ In (lo, len) (sec_extents ly S)).
{ unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
- left. apply in_flat_map in Hin as (c & Hc & Hin). apply zseq_In in Hc.
pose proof (region_in_prim ly c LY ltac:(zlia)) as (R1 & R2 & R3 & R4 & R5).
pose proof (wf_classes _ _ _ _ _ WF c ltac:(zlia)) as CL. pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_fa _ _ _ _ _ _ CL) as [A2 _].
pose proof (wr_fa_bound _ _ _ _ _ _ CL) as A3. pose proof (mapped_user_bound (as_universe B) 0 0 0 S c WF ltac:(zlia)) as MB.
pose proof (lo_prim_al ly LY) as PA. unfold page_aligned in PA. apply Z.mod_divide in PA as [pp Hpp]; [|zlia]. apply Z.mod_divide in Hg8 as [q Hq]; [|zlia].
unfold kUserMapSize, EV_MAX, kFreeArrayMax, kPrimResvSize in *. unfold fa_base, kFreeArrayOffset in Hin. unfold region_base in *.
destruct Hin as [E|[E|[]]]; injection E as <- <-; clear - Hglo R1 R2 A1 A2 A3 MB Hpp Hq MZ; zlia.
- right. apply in_flat_map in Hin as (k & Hk & Hin). unfold sec_extents. apply in_flat_map. exists k. exact (conj Hk Hin). }
assert (GB : in_band_rw (shadow_addr g)).
{ destruct GZ as [[X1 X2]|Hin'].
- assert (HPA : in_app (ly_prim ly) kPrimResvSize) by (unfold in_app; clear - F3 F6 MZ; zlia).
rewrite <- (Zplus_minus (ly_prim ly) g). apply (shadow_addr_in_band _ _ _ HPA). clear - X1 X2 MZ. zlia.
- pose proof (am_placed _ _ _ _ MA) as [PL _]. pose proof (proj1 (Forall_forall _ _) PL (lo, len) Hin') as (_ & HIA & _). cbn [fst snd] in HIA.
rewrite <- (Zplus_minus lo g). apply (shadow_addr_in_band _ _ _ HIA). clear - Hglo MZ. zlia. }
apply Z_band; [exact GB|]. apply sh_sep; [exact Hg8|].
destruct GZ as [[X1 X2]|Hin'].
-- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - X1 X2 MP3 MZ. zlia.
-- pose proof (proj1 (Forall_forall _ _) GAPART (lo, len) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin')) as D. unfold zdisjoint in D. cbn [fst snd] in D.
apply Z.mod_divide in Hg8 as [q Hq]; [|zlia]. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. clear - Hglo D Hq Hp MZ. zlia.
* cbn [orb in_rangesb] in HV. rewrite Bool.orb_false_r in HV.
destruct (andb (mb <=? g) (g <? mb + MSv)) eqn:IM; [|discriminate HV]. injection HV as <-.
apply andb_prop in IM as [IM1 IM2]. apply Z.leb_le in IM1. apply Z.ltb_lt in IM2.
apply Bool.andb_false_iff in CK. rewrite M4 in CK.
assert (GH : g < mb + 4096) by (destruct CK as [CK|CK]; [apply Z.leb_gt in CK | apply Z.ltb_ge in CK]; clear - CK IM1 IM2 MZ; zlia).
set (j := (g - mb) / 8).
assert (Hgj : g = mb + 8 * j).
{ subst j. pose proof (Z.div_mod (g - mb) 8 ltac:(zlia)) as D1. apply Z.mod_divide in M3 as [p Hp]; [|zlia]. apply Z.mod_divide in Hg8 as [q Hq]; [|zlia].
assert ((g - mb) mod 8 = 0) by (rewrite Hq, Hp; replace (q * 8 - p * 4096) with ((q - 512 * p) * 8) by zlia; apply Z.mod_mul; zlia). zlia. }
rewrite Hgj, sh_map. apply rd_byte; [unfold shHeapLeftRz; zlia | apply sh_vis; clear - IM1 GH Hgj Z8 DM8 M8 MZ; zlia |].
apply Vsh. rewrite unsigned_lit_small by (clear - IM1 GH Hgj SM1 SM2 Z8 MZ; unfold kHighShadowBeg, kHighShadowEnd in *; zlia). left. clear - IM1 GH Hgj MZ. zlia.
Qed.
Lemma Z_lowsh : forall a, 2147459072 <= a < 2148234240 -> ~ XC a.
Proof.
intros a Ha Hx. apply XC_where in Hx. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & _). pose proof map_facts as (M1 & _). pose proof map_zoneN as MZ.
pose proof (zone3_apart_img _ _ a F1) as TI. pose proof (zone3_apart_hsh _ _ a F1) as TH. pose proof (zone3_apart_img _ _ a F9) as QI. pose proof (zone3_apart_hsh _ _ a F9) as QH. pose proof (zone3_apart_img _ _ a NBhi) as NI. pose proof (zone3_apart_hsh _ _ a NBhi) as NH. pose proof (zone3_apart_img _ _ a SBhi) as BI. pose proof (zone3_apart_hsh _ _ a SBhi) as BH. pose proof (zone3_apart_img _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MI. pose proof (zone3_apart_hsh _ _ a (mzone_zone3 _ _ (proj2 Hmap))) as MH. unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize, kPtrArrayResv, kNodesBlockSize, kStoreBlockSize in TI, TH, QI, QH, NI, NH, BI, BH, MI, MH.
clear - Ha Hx TH QH NH BH MH MZ. numconst. unfold kHighShadowBeg, kHighShadowEnd in *. try unfold T in *. try unfold Qb in *.
decompose [and or] Hx; clear Hx; zlia.
Qed.
Lemma zshadow_final : zshadow_ok B lyF rd'.
Proof.
pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E10 & E11 & _).
unfold zshadow_ok. replace (zero_shadow_ranges B lyF) with (zero_shadow_ranges B ly) by (unfold zero_shadow_ranges; rewrite E10, E11; reflexivity).
apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
apply AGX; [eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] | | exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)].
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (lo_stk_ceil ly LY) as SC. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
-
cbn [fst snd] in *.
pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(zlia)) as D1. pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as D2.
pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(zlia)) as B2.
assert (A8 : ly_stk_lo ly mod 8 = 0) by (unfold page_aligned in T5; apply Z.mod_divide in T5 as [q Hq]; [|zlia]; rewrite Hq; replace (q * 4096) with (q * 512 * 8) by zlia; apply Z.mod_mul; zlia).
apply Z_band.
+ unfold in_band_rw, shadow_addr. clear - Hi T1 T2 T4 T7 D1 D2 B2 A8 SC MZ. numconst. unfold SHADOW_OFF, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd. zlia.
+ apply Z.mod_divide in A8 as [q Hq]; [|zlia].
pose proof (sh_sep (ly_stk_lo ly + 8 * i) ltac:(rewrite Hq; replace (q * 8 + 8 * i) with ((q + i) * 8) by zlia; apply Z.mod_mul; zlia) ltac:(right; clear - Hi SC M2 D1 D2 B2 MZ; numconst; zlia)) as NS.
unfold shadow_addr in NS |- *. rewrite Hq in NS |- *. replace (q * 8 + 8 * i) with ((q + i) * 8) in NS by zlia. replace (q * 8) with (q * 8) by zlia.
rewrite Z.div_mul in NS by zlia. replace (q * 8 / 8) with q by (symmetry; apply Z.div_mul; zlia). clear - NS MZ. zlia.
-
pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr) as (Z1 & Z2 & Z3 & Z4 & Z5).
assert (RI : 0x10000 <= fst r /\ fst r + snd r <= 0x5fa000).
{ rewrite (ts_zsh B TS) in Hr. unfold Tfib_zero_shadow in Hr. cbn [In] in Hr. clear - Hr MZ.
repeat destruct Hr as [<-|Hr]; try contradiction; cbn [fst snd]; zlia. }
apply Z_lowsh. unfold shadow_addr. unfold kLowMemEnd in Z5.
pose proof (Z.div_mod (fst r) 8 ltac:(zlia)) as D1. pose proof (Z.div_mod (snd r) 8 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(zlia)) as B1.
clear - Hi Z1 Z2 Z3 Z4 Z5 RI D1 D2 B1 MZ. unfold SHADOW_OFF. zlia.
Qed.
Lemma SEF : sec_extents lyF SF = sec_extents ly S ++ [(mb, MSv)].
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold sec_extents at 1. rewrite Rck, flat_map_app. pose proof (sec_extents_le ly lyF S _ _ _ _ lyF_le WF) as SE. unfold sec_extents in SE at 1. rewrite SE.
cbn [flat_map]. rewrite KB, KQ, MS, lyF_sec, app_nil_r. reflexivity.
Qed.
Lemma staticF : static_extents lyF = static_extents ly /\ vis0_zones lyF = vis0_zones ly /\ core_extents lyF = core_extents ly /\ owned_extents lyF = owned_extents ly.
Proof. clearP. unfold lyF, set_ly_sec, static_extents, vis0_zones, core_extents, owned_extents. cbn. repeat split; reflexivity. Qed.
Lemma placed_finalG : Forall (zdisjoint (mb, MSv)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) -> sec_placed lyF SF.
Proof.
clear GAPART. intros GAPART.
pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof map_facts as (M1 & M2 & M3 & _). pose proof map_zoneN as MZ. pose proof staticF as (ES & _).
unfold sec_placed. rewrite SEF, ES. split.
- apply Forall_app. split; [exact PL|]. constructor; [|apply Forall_nil]. cbn [fst snd]. unfold page_aligned, in_app.
clear - M1 M2 M3 MZ. ceil. unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, TFIB_IMG_END in *. repeat split; zlia.
- apply pairwise_app_inv in PD as (P1 & P2 & P3). apply pairwise_app; [apply pairwise_app; [exact P1 | cbn; split; [apply Forall_nil | exact I] |] | exact P2 |].
+ intros x y Hx [<-|[]]. apply zdisjoint_sym. apply (proj1 (Forall_forall _ _) GAPART). rewrite !in_app_iff. right; right. exact Hx.
+ intros x y Hx Hy. apply in_app_iff in Hx as [Hx|[<-|[]]]; [exact (P3 x y Hx Hy)|].
apply (proj1 (Forall_forall _ _) GAPART). rewrite !in_app_iff. left. exact Hy.
Qed.
Lemma placed_final : sec_placed lyF SF.
Proof. exact (placed_finalG GAPART). Qed.
Lemma vis_old : forall lst, incl lst (ajunk B ly S) \/ incl lst (aareas S) \/ incl lst (aclient S) -> Forall (range_vis B lyF rd') lst.
Proof.
intros lst H. apply (Forall_range_vis_le B ly lyF _ lyF_le rd').
- destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]);
[exact (AFib_w.ajunk_lt B ly S _ _ _ _ WF (JUNKlt _ ly)) | exact (AFib_w.aareas_lt S _ _ _ _ WF) | exact (AFib_w.aclient_lt S _ _ _ _ WF)].
- apply (Forall_range_vis_keep B ly rd0 rd' lst VIS_MONO).
destruct H as [H|[H|H]]; (eapply incl_Forall; [exact H|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Lemma vis_map : forall e len, mb <= aeval B lyF e -> aeval B lyF e + len <= mb + MSv -> range_vis B lyF rd' (e, len).
Proof. intros e len H1 H2 i Hi. cbn [fst snd] in Hi |- *. apply apresent_vis. apply PRmap. clear - H1 H2 Hi. zlia. Qed.
Lemma resF_facts : Z.of_nat (length (st_sec_arr S)) + 1 <= (if grow then res + kPtrArrayEntriesPerCommit else res) <= kPtrArrayEntriesPerCommit /\
(grow = false -> idx < res).
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & Rarr & Rres & _).
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ (proj1 MP))) as WR. rewrite Rarr, Rres, length_app in WR. cbn [length] in WR.
pose proof len_arr as LA. pose proof Hres as [HRS _]. split; [zlia|]. intros Hg. destruct (Z.eq_dec idx res) as [E|NE]; [|zlia].
exfalso. pose proof (proj2 Hgrow E) as Hg'. rewrite Hg in Hg'. discriminate Hg'.
Qed.
Lemma vis_junk : Forall (range_vis B lyF rd') (ajunk B lyF SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS. pose proof lyF_eqs as (_ & _ & EQ & _).
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _). pose proof len_arr as LA. pose proof resF_facts as [RF1 RF2].
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
assert (EV2 : forall d d', aeval B lyF (aoff (ASec (rS S) d) d') = mb + d + d') by (intros d d'; cbn [aeval aoff]; rewrite LS; zlia).
unfold ajunk. rewrite Rck.
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. right; left. reflexivity. }
apply Forall_app; split; [apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; apply in_app_iff; left; exact Hx|].
apply Forall_app; split.
{ replace (flat_map (cache_junk SF) (zseq 1 31)) with (flat_map (cache_junk S) (zseq 1 31)) by (apply flat_map_ext; intros c; unfold cache_junk; rewrite Rinit, (Rcache c); reflexivity).
apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. apply in_app_iff; right. apply in_app_iff; left. exact Hx. }
apply Forall_app; split.
{ rewrite flat_map_app. apply Forall_app; split.
- apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 2 (apply in_app_iff; right). apply in_app_iff; left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_junk. rewrite KR, KN, KST, KB, KE. unfold kChunkHeaderSize. cbn [sptr_exp app Z.eqb Pos.eqb].
repeat (apply Forall_cons; [apply vis_map; rewrite EV2; clear - Z1 Z3 Z7 Z10; zlia|]). apply Forall_nil. }
apply Forall_app; split.
{ unfold sec_junk. rewrite Rarr, Rres, Rck, flat_map_app, length_app. cbn [length].
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left. unfold sec_junk. left. reflexivity. }
apply Forall_cons. { refine (proj1 (Forall_forall _ _) (vis_old [_] _) _ (or_introl eq_refl)). left. intros x [<-|[]]. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left. unfold sec_junk. right; left. reflexivity. }
apply Forall_cons.
{
intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ. replace (Z.of_nat (length (st_sec_arr S) + 1)) with (idx + 1) in Hi |- * by zlia.
destruct (Z_lt_le_dec (Qb + 8 * (idx + 1) + i) (Qb + 8 * res)) as [LO|HI].
- pose proof (proj1 (Forall_forall _ _) (am_junk _ _ _ _ MA) (AQ (8 * Z.of_nat (length (st_sec_arr S))), 8 * (st_sec_reserved S - Z.of_nat (length (st_sec_arr S))))
ltac:(unfold ajunk; do 2 right; do 3 (apply in_app_iff; right); apply in_app_iff; left; unfold sec_junk; do 2 right; left; reflexivity)) as RV.
specialize (RV (8 + i)). cbn [fst snd aeval] in RV. rewrite <- Hres_def, LA in RV. apply VIS_MONO.
replace (Qb + 8 * (idx + 1) + i) with (ly_Q ly + 8 * idx + (8 + i)) by (unfold Qb; zlia). apply RV. clear - Hi LO. unfold Qb in *. zlia.
- apply apresent_vis. destruct grow eqn:Eg; [| pose proof (RF2 eq_refl); exfalso; clear - Hi HI RF1 H; zlia].
apply (PRq eq_refl). unfold QR. clear - Hi HI RF1 F9 F10. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. try unfold Qb in *. zlia. }
apply Forall_app; split.
- apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 3 (apply in_app_iff; right). apply in_app_iff; left. unfold sec_junk. do 3 right. exact Hx.
- cbn [flat_map]. rewrite KB, app_nil_r. constructor; [|apply Forall_nil]. apply vis_map; cbn [aeval]; rewrite LS; unfold kPage; clear - Z8; zlia. }
apply Forall_app; split.
{ apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 4 (apply in_app_iff; right). apply in_app_iff; left.
unfold quar_junk, all_batches in *. rewrite Rqt, Rqg in Hx. exact Hx. }
apply Forall_app; split; [apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; do 5 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
apply Forall_app; split; [apply vis_old; left; intros x Hx; unfold ajunk; do 2 right; do 6 (apply in_app_iff; right); apply in_app_iff; left; exact Hx|].
rewrite (JUNK lyF ly). apply vis_old. left. intros x Hx. unfold ajunk. do 2 right. do 6 (apply in_app_iff; right). apply in_app_iff; right. exact Hx.
Qed.
Lemma vis_areas : Forall (range_vis B lyF rd') (aareas SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS. pose proof lyF_eqs as (_ & _ & EQ & _).
pose proof resF_facts as [RF1 RF2]. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _). pose proof len_arr as LA.
unfold aareas. rewrite Rres, Rck, flat_map_app.
apply Forall_app; split.
{ unfold reg in Rreg |- *.
apply vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff. left. exact Hx. }
apply Forall_cons.
{ intros i Hi. cbn [fst snd aeval] in Hi |- *. rewrite EQ.
destruct (Z_lt_le_dec i (8 * res)) as [LO|HI].
- pose proof (proj1 (Forall_forall _ _) (am_areas _ _ _ _ MA) (AQ 0, 8 * st_sec_reserved S) ltac:(unfold aareas; apply in_app_iff; right; left; reflexivity)) as RV.
specialize (RV i). cbn [fst snd aeval] in RV. rewrite <- Hres_def in RV. apply VIS_MONO. apply RV. clear - Hi LO. zlia.
- apply apresent_vis. destruct grow eqn:Eg; [| exfalso; clear - Hi HI; zlia].
apply (PRq eq_refl). unfold QR. clear - Hi HI RF1 F9 F10 LA. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. try unfold Qb in *. zlia. }
apply Forall_app; split.
{ apply Forall_app; split.
- apply vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. exact Hx.
- cbn [flat_map]. rewrite KB, KQ, MS, app_nil_r. constructor; [|apply Forall_nil]. apply vis_map; cbn [aeval]; rewrite LS; zlia. }
apply vis_old. right; left. intros x Hx. unfold aareas. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.
Lemma vis_client : Forall (range_vis B lyF rd') (aclient SF).
Proof.
pose proof SF_parts as (Rreg & Rinit & Rcache & Rfr & Rqt & Rqg & Rfs & Rii & Rarr & Rres & Rdep & Rck & _).
pose proof sizes_model as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof lyF_sec as LS.
pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).
unfold aclient. rewrite Rfr, Rck, flat_map_app.
apply Forall_app; split; [apply Forall_app; split|].
- apply vis_old. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. left. exact Hx.
- cbn [flat_map]. rewrite app_nil_r. unfold chunk_user. rewrite KST, KN. unfold ck_user. rewrite KB. change (YG00.ck_rz KSc) with (ck_rz KSc). rewrite KR. cbn [padd sptr_exp].
constructor; [|apply Forall_nil]. apply vis_map; cbn [aeval]; rewrite LS; clear - Z1 Z3 Z7 Z10; zlia.
- apply vis_old. do 2 right. intros x Hx. unfold aclient. apply in_app_iff. right. exact Hx.
Qed.
Lemma depot_okF : forall s1 s2 (rd : reader), st_depot s1 = st_depot s2 -> depot_ok B ly rd s1 -> depot_ok B lyF rd s2.
Proof.
clearP. intros s1 s2 rd E. pose proof lyF_eqs as (_ & _ & _ & _ & _ & _ & E7 & _ & _ & _ & _ & _ & E13 & _).
unfold depot_ok, depot_ids, depot_traces. rewrite E, E7, E13. exact (fun H => H).
Qed.
Lemma ARm_final : ARm B lyF SF rd'.
Proof.
pose proof MAF as MF. destruct MF as [_ Mun Msy Mly _ _ Mcow _ _ _ _ _ _ _ _ _ _ Mts Msi].
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rdep & _).
constructor.
- exact (proj1 MP).
- exact Mun.
- exact Msy.
- exact Mly.
- exact placed_final.
- exact const_finalF.
- exact Mcow.
- exact cells_final.
- exact fa_final.
- exact flags_final.
- apply (depot_okF (depot_after z tr S)); [rewrite Rdep; unfold depot_after; destruct (z =? 0); reflexivity | exact (proj1 (proj2 depot_final))].
- exact shadow_final.
- exact zshadow_final.
- exact vis_junk.
- exact vis_areas.
- exact vis_client.
- exact zero_final.
- exact Mts.
-   exact Msi.
Qed.
Lemma ahs_final : ahs B lyF SF (w_H Wz) mem'.
Proof.
pose proof HAR as (_ & _ & _ & _ & [HS0 HZ0]). pose proof SF_parts as (_ & _ & _ & Rfr & _ & _ & _ & _ & _ & _ & _ & Rck & _).
pose proof staticF as (ES & EV0 & _). pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & E16).
split.
- intros a Ha NC HV. apply (BANDKEEP a Ha). apply (HS0 a Ha).
+ intros CL. apply NC. destruct CL as [(k & Hk & Hst & Hr) | (cp & Hcp & Hr)].
* left. exists k. split; [rewrite Rck; apply in_app_iff; left; exact Hk | split; [exact Hst|]].
unfold ck_user. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (AFib_w.padd_lt S _ _ (AFib_w.chunk_lt S _ _ _ _ WF k Hk))). exact Hr.
* right. exists cp. split; [unfold frames in Hcp |- *; cbn; exact Hcp|]. unfold frame_addr in Hr |- *. rewrite E6. exact Hr.
+ destruct HV as [Hh|Hv]; [left | right].
* destruct (w_H W (YG0n_w.w64 a)) eqn:E; [reflexivity|]. rewrite (MONf _ E) in Hh. discriminate Hh.
* unfold in_vis0 in Hv |- *. rewrite E16 in Hv. exact Hv.
- intros g Hg Happ HF.
unfold hfree in HF. rewrite SEF, ES, EV0 in HF. rewrite !app_assoc in HF. apply Forall_app in HF as [HF1 HF2].
pose proof (Forall_inv HF2) as X. cbn [fst snd] in X.
assert (HF0 : hfree ly S g) by (unfold hfree; rewrite !app_assoc; exact HF1). rewrite <- (HZ0 g Hg Happ HF0). exact (ZKEEP g Hg Happ X).
Qed.
Lemma sec_live_final : sec_live_bytes SF = sec_live_bytes S + MSv.
Proof.
pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rck & _). pose proof sizes_model as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold sec_live_bytes. rewrite Rck, fold_right_app. cbn [fold_right]. rewrite KB, KQ, MS.
assert (G : forall l a, fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) a l =
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l + a).
{ clear. induction l as [|k t IH]; intros a; cbn [fold_right]; [zlia|]. rewrite (IH a), (IH 0). destruct (ck_beg k); zlia. }
rewrite G. zlia.
Qed.
Theorem AR_transport : AR tfibsegs B lyF SF Wz mem' mdf.
Proof.
pose proof HAR as (_ & _ & BUD & _ & _). pose proof SF_parts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rsecs & Rnev & _).
split; [exact ARm_final|]. split; [exact LEDf|]. split; [|split; [exact MWf | exact ahs_final]].
pose proof (SH_hull mb) as (_ & _ & H3 & _). pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)) as MB8.
pose proof ABf as AB. pose proof sec_live_final as SLF. pose proof HINC as HINC'. pose proof AMAP as AMAP'. pose proof AHULL as AHULL'. pose proof SEF as SEF'.
destruct BUD as [BUD PIN]; split;
[ unfold abudget, sec_hulls in BUD |- *; rewrite Rnev, Rsecs, sec_hulls_app1, SLF, AB; cbn [sm_len]  ; clear - BUD H3 Z8 DM8 MB8; unfold EV_A, MALLOC_MAX in *; destruct grow; zlia
| intros e He; rewrite SEF' in He; apply in_app_iff in He as [He|[He|[]]];
[ split; [exact (HINC' _ (proj1 (PIN e He))) | exact (HINC' _ (proj2 (PIN e He)))]
| rewrite <- He; split; [cbn [fst snd]; exact AMAP' | unfold YG0n_w.shull; cbn [fst snd]; exact AHULL'] ] ].
Qed.
End c0.
Definition S_AR_final := AR_transport.
End b0.
End f.
