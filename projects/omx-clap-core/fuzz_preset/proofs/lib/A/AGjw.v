(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjw.v (a working branch 84ee52cd012, file sha256 0858e9556f6f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 16 image addresses moved by code-verified function pairs (15 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at d1f93c50c87) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc 0474699fc83547e0 (a working branch 83209f9d9cd8), --assume-source, --resolve the internal file resolve-102.txt (1 line name this file); 15 numerals changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AB1q AFhy AGhy AGhz AGi0 AGi4 AGi9 AB1h AGjm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require AGif2.
(* the cgif instance of the image class (a9's image split): [world tfibsegs] unifies with [world im_segs] *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
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
Hypothesis Hinst : 0xa1000 <= INSTv /\ INSTv + 0xe60 <= 0x12d120 /\ INSTv mod 8 = 0.
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
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
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
Local Abbreviation cell_sym := (AGif2.sv_cell_sym B W ly INSTv mem0 idx res TS SV).
Local Abbreviation cell_lit := (AGif2.sv_cell_lit B W ly INSTv mem0 idx res TS SV).
Local Abbreviation rw_writable := (@AGjm.img_rw_writable ly regs0 tr idx res mb Htrlen Hidx).
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
RUN HR tbl tblok 0x54b60 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x549b8 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54b60 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54ba0 Sh3 HX HP;
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
RUN HR tbl tblok 0x54b60 Sl HX HP;
s_armR HR BC_GEU true (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZLO|];
RUN HR tbl tblok STOP Slo HX HP;
s_join HR k clob SJ
| s_armR HR BC_GEU false (14%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x549b8 Sh HX HP;
s_armR HR BC_LTU true (7%bv : bv 5) (10%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54b60 Sh2 HX HP;
s_armR HR BC_GEU false (14%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54b9c Sh3a HX HP;
s_armR HR BC_LTU false (6%bv : bv 5) (11%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x54ba0 Sh3 HX HP;
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
RUN HR tbl tblok 0x32ad8 Sh HX HP;
s_armR HR BC_LTU false (17%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok 0x32adc Sh2 HX HP;
s_armR HR BC_GEU false (16%bv : bv 5) (22%bv : bv 5); [ladder_arith ZHI|];
RUN HR tbl tblok STOP Shi HX HP;
s_join HR k clob SJ ]
| clear HR; eapply SRr_bind; [exact HQ | clear HQ; let W2 := fresh "WL" in let c2 := fresh "cL" in intros W2 c2 _ HR ] ]
end.
Let m0 := mrestrict (w_H W) mem0.
Lemma val_mem_mod8 : forall m a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x H k Hk. rewrite (H k Hk). do 2 f_equal. rewrite <- (le_byte_eq x), <- (le_byte_eq (x mod 2 ^ 64)). unfold YG0f.le_byte.
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Z.mod_mod by zlia. reflexivity.
Qed.
Lemma chunk_lit : forall a (nn : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | rewrite Z.add_0_l; exact H]. Qed.
Lemma chunk_lit_at : forall base a (nn : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SLit x))).
Proof. intros base a nn x H Hx Hnn. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hnn | exact H]. Qed.
Lemma chunk_atom : forall base a (nn : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat nn) x -> 0 <= x < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal nn (SOff k d))).
Proof.
intros base a nn k d x Hk Hr H Hx Hnn. eapply chunk_ok_val; [| exact Hx | exact Hnn | exact H].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. zlia.
Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac lit_region :=
reg_intro; split; [zlia|]; split; [zlia|]; split; [intros o Ho; zlia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; zlia | cbn; zlia] |]); apply Forall_nil.
Local Ltac uoffs := unfold zone3, TFIB_IMG_LO, kLowShadowBeg, o_sec, o_sec_chunks, o_sec_reserved, o_sec_n, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, kPtrArrayResv, TFIB_IMG_END in *.
Local Ltac junk_atom_chunk k j Hj :=
apply (chunk_atom _ _ 8 k 0 (j mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j (2 ^ 64)); zlia | apply val_mem_mod8; first [exact Hj | rewrite Z.add_0_r; exact Hj] | cbn; pose proof (Z.mod_pos_bound j (2 ^ 64)); zlia | cbn; zlia].
(* The regions of AGi9.SREG0 hold at the seed: the stack object, the scratch window and the empty slot, the
   image literals, the instance's fields at INSTv (from the view SV), the thread's and the instance's windows. *)
Lemma SREG0_ok : Forall (region_ok tfibsegs E0 m0) SREG0.
Proof.
pose proof high_facts as (hf1 & hf2 & hf3 & hf4 & hf5 & hf6 & hf7 & hf8 & hq1 & hq2 & hqa & hta & hsa & hca & hf9).
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). destruct Hsp as (S1 & S2 & S3 & S4).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kPtrArrayResv, t_cache, t_unwinding in hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hq1, hq2, T2, T4, T7.
pose proof tr_length as TL.
pose proof SV as [SLY SIMG STSD SCONST SSPACE SE20 SE28 SPAGE SCH SCH80 SRESV SRES SN SMTX SUNW STP SSP SCP SQ SIX SRB].
(* a9's image split: the view's fields mention the image class's projections; at cgif's instance they are cgif's
   values by delta, and the script below rewrites with them, so normalise them once *)
cbn [ImgBase.im_segs ImgBase.im_tsd ImgBase.im_img_cover AImg_A] in SIMG, STSD, SCONST, SSPACE, SE20, SE28, SPAGE, SCH, SCH80, SRESV, SRES, SN, SMTX, SUNW, STP, SSP, SCP, SQ.
(* lia reads every hypothesis and case-splits on each disjunction and each [_ mod _] it finds (the internal file common.md 'Proof
   speed' (2)). Clear the section hypotheses SREG0_ok is not stated over and the alignment facts no step needs,
   then restate by conversion only ([change]) what lia would split on: a disjunction or a [zone3cases] behind
   [id], a fact [a mod b = c] as [snd (Z.div_eucl a b) = c] (the body of [Z.modulo]), which zify does not open.
   Unhide with [unfold id in H] or [change (a mod b = c) in H]. SREG0_ok is stated over Hbp (its dependents pass
   it); the old script used Hbp only inside lia certificates, which no longer need it, so use it once here to
   keep the statement. *)
clear Hn Htp Hra Hra4096 Hmap Hmap_apart Hgp HQT S4 hqa hta hsa hca SRB.
unfold kPtrArrayEntriesPerCommit, kMaxNumChunks in Hres.
pose proof Hbp as Hbp_kept; clear Hbp_kept.
let rec rs_hide_t T := lazymatch T with
| ?A /\ ?B => let A' := rs_hide_t A in let B' := rs_hide_t B in constr:(A' /\ B')
| _ \/ _ => constr:(id T)
| zone3cases _ _ => constr:(id T)
| ?a mod ?b = ?c => constr:(snd (Z.div_eucl a b) = c)
| _ => T end in
repeat match goal with H : ?T |- _ => let T' := rs_hide_t T in assert_fails (constr_eq T T'); change T' in H end.
assert (EI : bv_unsigned (ew E0 11) = INSTv) by (rewrite (Er 11 11%bv eq_refl); reflexivity).
assert (ESO : bv_unsigned (ew E0 13) = SOv) by (rewrite (Er 13 13%bv eq_refl); reflexivity).
(* the instance's stats words at the offsets of the seed's chunks *)
assert (Hi2' : val_mem tfibsegs m0 (INSTv + 152) 8 i2) by (eapply AGjm.val_mem_addr; [exact Hi2 | unfold o_sec_stats; lia]).
assert (Hi3' : val_mem tfibsegs m0 (INSTv + 160) 8 i3) by (eapply AGjm.val_mem_addr; [exact Hi3 | unfold o_sec_stats; lia]).
assert (Hj6' : val_mem tfibsegs m0 (INSTv + 704) 8 j6) by (eapply AGjm.val_mem_addr; [exact Hj6 | unfold o_comb_stats; lia]).
assert (Hj7' : val_mem tfibsegs m0 (INSTv + 712) 8 j7) by (eapply AGjm.val_mem_addr; [exact Hj7 | unfold o_comb_stats; lia]).
unfold SREG0, TAIL0G, R_soG, R_scrG, R_slotG, lit1, lit4, lit8, lits8, atom8, ilit8, iatom8, ilits8, iatom8w, CTZ_TABLE, R_bsl.
cbn [firstn app map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ0, aJ1, aJ2, aJ3, aJ4, aJ5, aJ6, aJ7, aJ8, aJ9, aI1, aI2, aI3, aQ, aRES, aNCH, aLEN, aR8, aINST, aSO, aBP.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{   reg_intro. rewrite ESO. pose proof (u64_range (getr regs0 13)) as U13.
split; [unfold SOv; zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom SOv 0 8 12%nat 0 BPv);
[ rewrite Z.sub_0_r, (Er 12 12%bv eq_refl); unfold w64, BPv; symmetry; apply Z_to_bv_bv_unsigned
| pose proof (u64_range (getr regs0 12)); unfold BPv; zlia | rewrite Z.add_0_r; exact PSO
| unfold BPv; pose proof (u64_range (getr regs0 12)); change (8 * Z.of_N 8) with 64; zlia | cbn; zlia ].
- apply (chunk_atom SOv 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | zlia | exact PLEN | change (8 * Z.of_N 8) with 64; zlia | cbn; zlia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- AFSTACK)); [rewrite E2; reflexivity | unfold AFSTACK; zlia | zlia |].
intros a Ha. apply apresent_writable_off; [off_by ltac:(unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, AFSTACK in *; zlia) | apply Hpres0; exact Ha]. }
(* the empty slot at the entry sp *)
apply Forall_cons.
{   reg_intro. rewrite E2. pose proof (u64_range (getr regs0 2)). split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia | apply Forall_nil]. }
do 8 (apply Forall_cons; [lit_region|]).
(* the instance's primary.space field *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom INSTv 32 8 34%nat 0 SB); [rewrite EaSB; unfold w64; f_equal; zlia | unfold SB; zlia | exact SSPACE | unfold SB; cbn; zlia | cbn; zlia]. }
(* the instance's words at +0xe20 *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; (apply chunk_lit_at; [first [exact SE20 | exact SE28] | cbn; zlia | cbn; zlia]). }
do 13 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 47%nat 0 SHBv); [reflexivity | unfold SHBv; zlia | | unfold SHBv; cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 7 (apply Forall_cons; [lit_region|]).
apply Forall_cons. {   reg_intro. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| cbn; zlia | cbn; zlia]. pose proof (cell_lit 0x5ddf00 8 0 ltac:(vm_compute; reflexivity)) as H8.
cbn [ImgBase.im_segs AImg_A] in H8.
intros k Hk. unfold m0. rewrite (H8 k ltac:(zlia)). rewrite !le_byte_zero. reflexivity. }
apply Forall_cons; [lit_region|].
apply Forall_cons. {   reg_intro. unfold TFIB_TP. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; zlia | cbn; zlia].
replace (6151920 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite STSD; unfold TFIB_TSD; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. unfold TFIB_TSD. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
rewrite Z.add_0_l. replace 6288024 with (aeval B ly (ATsd 0)) by (cbn; rewrite STSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaC. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; unfold T; zlia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; zlia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP; unfold w64; f_equal; zlia | zlia | | cbn; zlia | cbn; zlia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; zlia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; zlia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP; unfold w64; f_equal; zlia | unfold kStackSpan; zlia | | unfold kStackSpan; cbn; zlia | cbn; zlia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; zlia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; zlia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; zlia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
(* the thread's stats windows: present by the view (sv_tpres) *)
(* each window below is in the thread object, so [off_T] gives it off the image (off_by would first try
   off_img_high, whose lia fails only after a long search) *)
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply off_T; unfold kThreadObjSize; zlia |].
apply STP. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 37%nat 0 (j0 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia | apply val_mem_mod8; exact Hj0 | cbn; pose proof (Z.mod_pos_bound j0 (2 ^ 64)); zlia | cbn; zlia]. }
(* the thread's unwinding flag (sv_unw) *)
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia. unfold t_unwinding.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply off_T; unfold kThreadObjSize; zlia |]. replace (ly_T ly + o) with (ly_T ly + 3168) by zlia.
pose proof SUNW as U.
eapply mbyte_off_apresent; [apply off_T; unfold kThreadObjSize; zlia |]. unfold t_unwinding in U. rewrite <- (Z.add_0_r (ly_T ly + 3168)). exact (U 0%nat ltac:(zlia)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [| cbn; zlia | cbn; zlia]. exact SUNW. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply off_T; unfold kThreadObjSize; zlia |].
apply STP. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- apply (chunk_atom _ _ 8 49%nat 0 (j1 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia | apply val_mem_mod8; exact Hj1 | cbn; pose proof (Z.mod_pos_bound j1 (2 ^ 64)); zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 50%nat 0 (j2 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia | apply val_mem_mod8; exact Hj2 | cbn; pose proof (Z.mod_pos_bound j2 (2 ^ 64)); zlia | cbn; zlia].
- apply (chunk_atom _ _ 8 51%nat 0 (j3 mod 2 ^ 64)); [rewrite Z.sub_0_r; apply Z_to_bv64_eq_mod; rewrite Z.mod_mod by zlia; reflexivity
| pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia | apply val_mem_mod8; exact Hj3 | cbn; pose proof (Z.mod_pos_bound j3 (2 ^ 64)); zlia | cbn; zlia]. }
uoffs. cbn [Z.add Z.mul Z.sub Pos.add Pos.mul Pos.succ Pos.sub].
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply off_T; unfold kThreadObjSize; zlia |].
apply STP. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- junk_atom_chunk 53%nat j4 Hj4.
- junk_atom_chunk 43%nat j5 Hj5. }
apply Forall_cons. {   reg_intro. rewrite EaT. unfold w64. rewrite unsigned_lit_small by zlia.
split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply off_T; unfold kThreadObjSize; zlia |].
apply STP. unfold T, t_cache_stats, t_unwinding in *; zlia. }
apply Forall_cons; [|apply Forall_nil]. junk_atom_chunk 57%nat j9 Hj9. }
(* the secondary allocator's fixed cells at INSTv (sv_page, sv_chunks, sv_chunks80, sv_resv88) *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact SPAGE | cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 39%nat 0 Qb); [rewrite EaQ; unfold w64; f_equal; zlia | unfold Qb; zlia | exact SCH | unfold Qb; cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 39%nat 0 Qb); [rewrite EaQ; unfold w64; f_equal; zlia | unfold Qb; zlia | exact SCH80 | unfold Qb; cbn; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [intros o Ho; zlia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact SRESV | cbn; zlia | cbn; zlia]. }
(* the counters: reserved slots (sv_res), live chunks (sv_n), the sorted flag *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply rw_writable. zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 40%nat 0 res); [rewrite EaRES; unfold w64; f_equal; zlia | destruct Hres as [HR _]; unfold kMaxNumChunks in *; zlia | exact SRES | cbn; destruct Hres as [HR _]; unfold kMaxNumChunks in *; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply rw_writable. zlia. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 41%nat 0 idx); [rewrite EaNCH; unfold w64; f_equal; zlia | unfold kMaxNumChunks in *; zlia | exact SN | cbn; unfold kMaxNumChunks in *; zlia | cbn; zlia]. }
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split; [|apply Forall_nil].
intros o Ho. apply rw_writable. zlia. }
(* the secondary's stats words *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply rw_writable. zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- junk_atom_chunk 58%nat i1 Hi1.
- junk_atom_chunk 59%nat i2 Hi2'.
- junk_atom_chunk 60%nat i3 Hi3'. }
(* the secondary's mutex is free (sv_mutex) *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply rw_writable. zlia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact SMTX | cbn; zlia | cbn; zlia]. }
(* the combined allocator's stats words *)
apply Forall_cons. {   reg_intro. rewrite EI. split; [zlia|]. split; [zlia|]. split.
{ intros o Ho. apply rw_writable. zlia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- junk_atom_chunk 44%nat j6 Hj6'.
- junk_atom_chunk 54%nat j7 Hj7'. }
apply Forall_cons; [lit_region|]. apply Forall_cons; [lit_region|]. apply Forall_cons; [lit_region|]. apply Forall_cons; [lit_region|].
(* the by_size_log cell of the instance *)
apply Forall_cons. {
assert (HB : INSTv + 296 <= BSLv <= INSTv + 400) by exact BSLv_range.
reg_intro. unfold aBSL. rewrite EaBSL. unfold w64. rewrite unsigned_lit_small by (clear - HB Hinst; zlia).
split; [clear - HB Hinst; zlia|]. split; [clear - HB Hinst; zlia|]. split.
{ intros o Ho. apply rw_writable. clear - HB Hinst Ho. zlia. }
apply Forall_cons; [|apply Forall_nil]. junk_atom_chunk 56%nat j8 Hj8. }
apply Forall_nil.
Qed.
End f.
End d.
About SREG0_ok.
