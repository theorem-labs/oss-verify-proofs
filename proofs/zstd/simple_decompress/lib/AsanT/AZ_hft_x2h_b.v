(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2 ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x2_kit AZ_hft_x2h_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
(* [comment removed for export] *)
Ltac kxk_sizes ::= rewrite ?length_map, ?Zupd_length, ?upd_length.

(* [comment removed for export] *)
Ltac kxv_reveal :=
  repeat match goal with
  | E : hidden (?v = ?e) |- _ =>
      first [ lazymatch e with context [ev _ _] => fail | context [edenot _ _] => fail | _ => idtac end; unfold hidden in E; subst v
            | let B := fresh "KB" in assert (B : 0 <= v < 256) by (unfold hidden in E; rewrite E; apply Z.mod_pos_bound; lia); clear E ]
  end.

Section CANSEC1. Context {rc : runConstT}.
Section H.
  (* [comment removed for export] *)
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem) (SPA DT SYM : Z).
  Variables (x2 x8 : word).     (* [comment removed for export] *)
  Variables (x1 x5 x6 x7 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word).                                    (* [comment removed for export] *)
  Variables (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : word).
  Variable syb : list byte.
  Variables (pos cnt bg nb T : Z).
  Hypothesis HY : x2hA_hyps RNG SPA DT SYM.
  Hypothesis UDT : unpoisoned m0 DT (DT + 16388).
  Hypothesis USY : unpoisoned m0 SYM (SYM + 256).
  Hypothesis ART0 : art m0.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis HPOS : 0 <= pos.
  Hypothesis HBG : 0 <= bg.
  Hypothesis HCNT : 0 <= cnt.
  Hypothesis HBC : bg + cnt <= 256.
  Hypothesis HNB : 0 <= nb <= T.
  Hypothesis HT : 1 <= T <= 12.
  Hypothesis HROOM : pos + 2^(T - nb) * cnt <= 4096.
  Hypothesis SL : x2h1_slots m0 SPA DT SYM bg cnt.
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide5 DT SYM SPA SPA SPA; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase5 DT SYM SPA SPA SPA lo1 in
                lazymatch goal with
                | U : unpoisoned mm X ?hi0 |- _ => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | match goal with
                | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
                end
              | kxa_unp_hook ]
    end.
  Local Ltac kxl_rng ::=
    first [ kxl_hyp
          | lazymatch goal with
            | |- rng ?RG ?A ?N =>
                let X := kxk_sbase5 DT SYM SPA SPA SPA A in
                lazymatch goal with H : rng RG X ?N0 |- _ => apply (rng_sub' RG X N0 A N H); solve [kx_lia] end
            end
          | lazymatch goal with
            | |- rng ?RG ?A ?N => match goal with H : rng RG ?A0 ?N0 |- _ => apply (rng_sub' RG A0 N0 A N H); solve [kxl_lia_small] end
            end
          | kx_rng ].
  Local Ltac kxa_rng0 ::=
    kxa_norm;
    lazymatch goal with
    | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
        first [ let X := kxk_sbase5 DT SYM SPA SPA SPA A in
                lazymatch goal with
                | H : rng RG (shad X) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | match goal with
                | H : rng RG (shad ?A0) ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n (shad A0) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                | H : rng RG ?A0 ?N0 |- _ =>
                    apply (shad_shspan_rng RG A n A0 N0 H);
                    [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                end
              | lazymatch RG with
                | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
                end
              | kxa_rng_hook ]
    end.
  (* [comment removed for export] *)
  Local Ltac h_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m0 => fail | _ => clear H end end;
    try match goal with H : art ?mx |- _ => lazymatch mx with m0 => fail | _ => clear H end end;
    repeat match goal with H : rw_cells _ _ (SPA + ?o) _ |- _ =>
      lazymatch o with 144 => clear H | 160 => clear H | 192 => clear H | 288 => clear H | 608 => clear H end end;
    lazymatch goal with
    | MU : munch _ m0 ?m2 |- _ =>
        pose proof (x2h_unp_dtM _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x2h_unp_syM _ _ _ _ _ HY USY m2 MU) as USY1;
        try lazymatch goal with WM : wmono _ m0 m2 |- _ =>
              pose proof (x2h_artM _ _ _ _ _ HY ART0 m2 MU WM) as ART1;
              destruct (x2h1_slots_tr _ _ _ _ _ HY _ _ m2 SL MU WM) as (S144 & S160 & S192 & S288 & S608) end
    | |- _ => idtac
    end.
  Local Ltac h_open :=
    open_hyh HY; unfold KHIGH in *;
    pose proof (x2h_bands _ _ _ _ HY) as (BDT & BSY & BSP & BSP2 & B5 & B6 & B7 & B8);
    hide_all_disj; h_reunp.
  (* [comment removed for export] *)
  Notation KZH := [KZRange SPA 0x10007fff8000 (2^47 - 728); KZRange DT 0x625000 (2^47 - 16388); KZRange SYM 0x625000 (2^47 - 257);
     KZAlign SPA 16; KZAlign DT 4; KZDisj DT 16388 SPA 728; KZDisj SYM 256 SPA 728; KZDisj DT 16388 SYM 256;
     KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12] (only parsing).
  Notation AKH := [KAUnp DT 16388; KAApp DT 16388; KAUnp SYM 256; KAApp SYM 256] (only parsing).
  (* [comment removed for export] *)
  Notation STH pc mm r1 r5 r6 r7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 r28 r29 r30 r31 :=
    (MS (mkR r1 x2 gp tp r5 r6 r7 x8 (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 0x7fff8000) xs9 xs10 xs11 r28 r29 r30 r31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation XHm dt mm := (XH SPA DT SYM m0 syb v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 dt mm) (only parsing).
  Notation XHs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 dt mm := (XH SPA DT SYM m0 syb w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 dt mm) (only parsing).

  (* [comment removed for export] *)
  Local Ltac h_lens :=
    try lazymatch goal with
    | DTC : u8arr _ _ DT (map _ ?d) |- _ =>
        first [ assert (zlen (map (Z_to_bv 8) d) = 16388) by assumption
              | assert (zlen (map (Z_to_bv 8) d) = 16388) by (rewrite length_map, ?Zupd_length2; lia) ]
    end.

  (* [comment removed for export] *)
  Local Ltac h_d64_bytes :=
    repeat match goal with
    | R : 0 <= bv_unsigned (ev ?EE ?j) <= 255, E : hidden (?v = (?P mod 2 ^ 64 / 65536) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | R : 0 <= bv_unsigned (ev ?EE ?j) <= 255, E : hidden (?v = (?P mod 2 ^ 64 / 65536 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = 1) by (rewrite E; clear - R HNB HT; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | R : 0 <= bv_unsigned (ev ?EE ?j) <= 255, E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | R : 0 <= bv_unsigned (ev ?EE ?j) <= 255, E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = 1) by (rewrite E; clear - R HNB HT; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    end;
    repeat match goal with H : ?v = nb |- _ => is_var v; subst v | H : ?v = 1 |- _ => is_var v; subst v end.
  (* [comment removed for export] *)
  Local Ltac h_pref1 c dt PRE :=
    replace (c + 1) with (c + Z.of_nat 1) by lia;
    eapply (prf2_close_c T c [0] _ 1%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref2 c dt PRE :=
    replace (c + 2) with (c + Z.of_nat 2) by lia;
    eapply (prf2_close_c T c [1; 0] _ 2%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref4 c dt PRE :=
    replace (c + 4) with (c + Z.of_nat 4) by lia;
    eapply (prf2_close_c T c [3; 2; 1; 0] _ 4%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [2; 1; 0] _ 3); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [2; 1; 0] _ 3); [| lia| lia| lia];
    eapply (prf2_st_nl T c [1; 0] _ 2); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [1; 0] _ 2); [| lia| lia| lia];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref8 c dt PRE :=
    replace (c + 8) with (c + Z.of_nat 8) by lia;
    eapply (prf2_close_c T c [7; 6; 5; 4; 3; 2; 1; 0] _ 8%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [6; 5; 4; 3; 2; 1; 0] _ 7); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [6; 5; 4; 3; 2; 1; 0] _ 7); [| lia| lia| lia];
    eapply (prf2_st_nl T c [5; 4; 3; 2; 1; 0] _ 6); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [5; 4; 3; 2; 1; 0] _ 6); [| lia| lia| lia];
    eapply (prf2_st_nl T c [4; 3; 2; 1; 0] _ 5); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [4; 3; 2; 1; 0] _ 5); [| lia| lia| lia];
    eapply (prf2_st_nl T c [3; 2; 1; 0] _ 4); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [3; 2; 1; 0] _ 4); [| lia| lia| lia];
    eapply (prf2_st_nl T c [2; 1; 0] _ 3); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [2; 1; 0] _ 3); [| lia| lia| lia];
    eapply (prf2_st_nl T c [1; 0] _ 2); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [1; 0] _ 2); [| lia| lia| lia];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  (* [comment removed for export] *)
  Local Ltac h_block L c dt PRE DTC DTLEN DTBY :=
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) =>
      let P' := fresh "PRE'" in let L' := fresh "DTLEN'" in let B' := fresh "DTBY'" in
      assert (P' : x2pref T (c + L) d) by (lazymatch L with 1 => h_pref1 c dt PRE | 2 => h_pref2 c dt PRE | 4 => h_pref4 c dt PRE | 8 => h_pref8 c dt PRE end);
      assert (L' : zlen d = 16388) by (rewrite !Zupd_length2; exact DTLEN);
      assert (B' : Forall isbyte d) by (repeat (apply Forall_Zupd; [| first [clear; lia| clear - HNB HT; lia| assumption| apply Z.mod_pos_bound; clear; lia]]); exact DTBY)
    end.

  (* [comment removed for export] *)
  Lemma rdn_sh0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
    rdn bsegs m (wa (shad p)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof. intros m X n p U Hp Hg. cbn [rdn]. rewrite (unp_shadow_zero m X n p U Hp Hg). reflexivity. Qed.

  (* [comment removed for export] *)
  Notation STC4 pc mm k qc base ya0 ya3 ys2 ys4 ys5 yt4 yt5 yt6 :=
    (STH pc mm x1 (Z_to_bv 64 (DT + 19 + 16 * k)) (Z_to_bv 64 (DT + 12 + 16 * k)) (Z_to_bv 64 (DT + 11 + 16 * k))
        ya0 (Z_to_bv 64 (4 * pos)) (Z_to_bv 64 (SYM + bg + k)) ya3 (Z_to_bv 64 (cnt - k)) (Z_to_bv 64 (2147450880 + qc))
        (Z_to_bv 64 base) (Z_to_bv 64 (DT + 4 + 16 * k)) ys2 (Z_to_bv 64 (SYM + bg + k)) ys4 ys5 x22 x23
        (Z_to_bv 64 pos) x26 x27 (Z_to_bv 64 (DT + 4 + 16 * k)) yt4 yt5 yt6)
    (only parsing).
  Notation STRET mm r1 r5 r6 r7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 r28 r29 r30 r31 :=
    (STH 0x97990 mm r1 r5 r6 r7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 r28 r29 r30 r31) (only parsing).
  Notation KRET c := (forall m2 (dt' : list Z) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31,
      XHs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 dt' m2 -> x2pref T c dt' ->
      evtF bsegs RNG POST (STRET m2 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31)) (only parsing).
  Notation STE pc mm len xa3 xa4 :=
    (STH pc mm x1 x5 x6 x7 (Z_to_bv 64 nb) (Z_to_bv 64 (4 * pos)) (Z_to_bv 64 len) xa3 xa4 x15 (Z_to_bv 64 bg) x17
         x18 (Z_to_bv 64 (SYM + bg)) x20 x21 x22 x23 (Z_to_bv 64 pos) x26 x27 x28 x29 x30 x31) (only parsing).


  (* [comment removed for export] *)
  Lemma x2h_c4l1_bodyB : forall m1 (dt : list Z) (k c qc : Z) xa0 xa3 xs2 xs4 xs5 xt4 xt5 xt6,
    XHm dt m1 -> T - nb = 2 -> 0 <= k < cnt -> c = pos + 4 * k -> qc = (DT + 4 + 4 * c) / 8 -> x2pref T c dt ->
    (forall m2 (dt' : list Z) (qc' : Z) ya0 ya3 ys2 ys4 ys5 yt4 yt5 yt6, k + 1 < cnt ->
       XHm dt' m2 -> qc' = (DT + 4 + 4 * (c + 4)) / 8 -> x2pref T (c + 4) dt' ->
       evtF bsegs RNG POST (STC4 0x992c4 m2 (k + 1) qc' (65536 * nb + 16777216) ya0 ya3 ys2 ys4 ys5 yt4 yt5 yt6)) ->
    (k + 1 = cnt -> KRET (pos + 4 * cnt)) ->
    evtF bsegs RNG POST (STC4 0x992c4 m1 k qc (65536 * nb + 16777216) xa0 xa3 xs2 xs4 xs5 xt4 xt5 xt6).
  Proof.
    intros until xt6; intros I HE HK HC HQ PRE KH KE. open_xh I. h_open. h_lens.
    assert (CR : 0 <= c /\ c + 4 <= 4096) by (pose proof HROOM as HR; rewrite HE in HR; change (2 ^ 2) with 4 in HR; subst c; lia).
    assert (QR : 0 <= qc < 17592186044416) by (subst qc; Z.div_mod_to_equations; lia).
    kx_autoFA AKH [0x992c4; 0x97990] 60%nat
      [KZRange SPA 0x10007fff8000 (2^47 - 728); KZRange DT 0x625000 (2^47 - 16388); KZRange SYM 0x625000 (2^47 - 257);
       KZAlign SPA 16; KZAlign DT 4; KZDisj DT 16388 SPA 728; KZDisj SYM 256 SPA 728; KZDisj DT 16388 SYM 256;
       KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12;
       KZRange k 0 255; KZRange (bg + k) 0 255; KZRange c 0 4092; KZRange (pos + 4 * k) 0 4092; KZRange qc 0 17592186044415; KZWord (2147450880 + qc) 1%nat 0; KZWr (DT + 4) 16384]
      [(SYM + bg + k, 1)] [(DT, 16388); (SYM, 256); (SPA, 728)].
    all: try (split; [lia| split; [lia| split; [lia|]]];
              replace (2147450880 + qc) with (shad (DT + 4 + 4 * c)) by (rewrite shad_div; unfold ASHOFF; subst qc; Z.div_mod_to_equations; lia);
              apply (rdn_sh0 m1 DT 16388); [exact UDT1| lia| Z.div_mod_to_equations; lia]).
    all: try lazymatch goal with
         | |- accP _ _ _ => pose proof RSDT as RSDTn; unfold shspan in RSDTn; rewrite !shad_div in RSDTn; unfold ASHOFF in RSDTn; kx_acc RSDTn
         | |- sc_resid _ _ _ (SCDisj _ _ _ _) =>
             kx_side_pre; pose proof BDT as BDT'; unfold hidden in BDT'; clear - BDT' B5 B7 CR HC HK HPOS;
             rewrite ?(Z.mod_small _ (2 ^ 64)) by lia; Z.div_mod_to_equations; lia
         end.
    all: kxk_keepg DTC. all: kx_mem. all: kx_read_ranges. all: h_d64_bytes. all: kxv_reveal. all: kx_tidy_run. all: clear KXUL0.
    all: h_block 4 c dt PRE DTC DTLEN DTBY.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x992c4) _ _ _ _) =>
             kx_setreg 5 (DT + 19 + 16 * (k + 1)); kx_setreg 6 (DT + 12 + 16 * (k + 1)); kx_setreg 7 (DT + 11 + 16 * (k + 1));
             kx_setreg 12 (SYM + bg + (k + 1)); kx_setreg 14 (cnt - (k + 1)); kx_setreg 15 (2147450880 + (qc + 2));
             kx_setreg 17 (DT + 4 + 16 * (k + 1)); kx_setreg 19 (SYM + bg + (k + 1)); kx_setreg 28 (DT + 4 + 16 * (k + 1));
             eapply KH; [lia| close_xh| subst qc; Z.div_mod_to_equations; lia| exact PRE']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97990) _ _ _ _) =>
             replace (c + 4) with (pos + 4 * cnt) in PRE' by lia;
             eapply (KE ltac:(lia) _ _ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9); [close_xh| exact PRE']
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2h_c4l1_loopB : forall (f : nat) m1 (dt : list Z) (k c qc : Z) xa0 xa3 xs2 xs4 xs5 xt4 xt5 xt6,
    XHm dt m1 -> T - nb = 2 -> 0 <= k < cnt -> cnt - k <= Z.of_nat f -> c = pos + 4 * k -> qc = (DT + 4 + 4 * c) / 8 -> x2pref T c dt ->
    KRET (pos + 4 * cnt) ->
    evtF bsegs RNG POST (STC4 0x992c4 m1 k qc (65536 * nb + 16777216) xa0 xa3 xs2 xs4 xs5 xt4 xt5 xt6).
  Proof.
    induction f as [|f IH]; intros until xt6; intros I HE HK HF HC HQ PRE KE; [lia|].
    eapply (x2h_c4l1_bodyB m1 dt k c); [exact I| exact HE| exact HK| exact HC| exact HQ| exact PRE| |].
    - intros m2 dt' qc' ya0 ya3 ys2 ys4 ys5 yt4 yt5 yt6 HK1 I2 HQ' PRE2.
      eapply (IH m2 dt' (k + 1) (c + 4)); [exact I2| exact HE| lia| lia| lia| exact HQ'| exact PRE2| exact KE].
    - intros HK1. exact KE.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma x2h_c4B : forall m1 (dt : list Z) xa3 xa4,
    XHm dt m1 -> T - nb = 2 -> x2pref T pos dt -> KRET (pos + 4 * cnt) ->
    evtF bsegs RNG POST (STE 0x99274 m1 4 xa3 xa4).
  Proof.
    intros until xa4; intros I HE PRE KE. open_xh I. h_open. h_lens.
    assert (P2 : 2 ^ (T - nb) = 4) by (rewrite HE; reflexivity).
    kx_autoFA AKH [0x992c4; 0x97990] 40%nat
      [KZRange SPA 0x10007fff8000 (2^47 - 728); KZRange DT 0x625000 (2^47 - 16388); KZRange SYM 0x625000 (2^47 - 257);
       KZAlign SPA 16; KZAlign DT 4; KZDisj DT 16388 SPA 728; KZDisj SYM 256 SPA 728; KZDisj DT 16388 SYM 256;
       KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12]
      (@nil (Z * Z)) [(DT, 16388); (SYM, 256); (SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97990) _ _ _ _) =>
             eapply (KE _ _ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9); [close_xh| replace (pos + 4 * cnt) with pos by lia; exact PRE]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
             kx_setreg 5 (DT + 19 + 16 * 0); kx_setreg 6 (DT + 12 + 16 * 0); kx_setreg 7 (DT + 11 + 16 * 0);
             kx_setreg 12 (SYM + bg + 0); kx_setreg 14 (cnt - 0); kx_setreg 16 (65536 * nb + 16777216);
             kx_setreg 17 (DT + 4 + 16 * 0); kx_setreg 19 (SYM + bg + 0); kx_setreg 28 (DT + 4 + 16 * 0);
             let v15 := StepF.reg_val 15 in lazymatch v15 with Z_to_bv 64 ?z15 =>
               replace (Z_to_bv 64 z15) with (Z_to_bv 64 (2147450880 + (DT + 4 + 4 * (pos + 4 * 0)) / 8))
                 by (f_equal; Z.div_mod_to_equations; lia) end;
             eapply (x2h_c4l1_loopB (Z.to_nat cnt) _ _ 0 (pos + 4 * 0));
             [close_xh| exact HE| lia| lia| reflexivity| reflexivity| replace (pos + 4 * 0) with pos by lia; exact PRE| exact KE]
         end.
  Qed.

End H.
End CANSEC1.
