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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x2_kit AZ_hft_x2h_defs  AZ_hft_x2h_a AZ_hft_x2h_b AZ_hft_x2h_c AZ_hft_x2h_d AZ_hft_x2h_e2.
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
  Local Ltac h_d64_bytes_with EL R HD :=
    let sq := lazymatch type of R with 0 <= ?q <= 255 => q | 0 <= ?q < 256 => q | 0 <= ?q < 65536 => q end in
    repeat match goal with
    | E : hidden (?v = (?P mod 2 ^ 64 / 65536) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT EL HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 65536 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = 1) by (rewrite E, EL; clear - R HNB HT HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT EL HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = 1) by (rewrite E, EL; clear - R HNB HT HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (_ = ((4294967297 * Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64)) mod 2 ^ 64 / 65536) mod 256) |- _ =>
        x2d_use nb 0 sq HNB R
    | E : hidden (_ = (Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64) / 65536) mod 256) |- _ =>
        x2w_use nb 0 sq HNB R
    | E : hidden (?v = ?X mod 256) |- _ =>
        lazymatch X with
        | context [ev _ _] => fail | context [edenot _ _] => fail
        | context [4294967297] => unfold hidden in E; subst v      (* [comment removed for export] *)
        | context [nb] =>
          unfold hidden in E;
          first [ let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT EL; Z.div_mod_to_equations; lia); clear E
                | let H := fresh "KV" in assert (H : v = 1) by (rewrite E, EL; clear - R HNB HT; Z.div_mod_to_equations; lia); clear E
                | subst v ]
        end
    end;
    repeat match goal with H : ?v = nb |- _ => is_var v; subst v | H : ?v = 1 |- _ => is_var v; subst v end.
  (* [comment removed for export] *)
  Local Ltac h_d64_bytes EL :=
    first [ match goal with R : 0 <= bv_unsigned (ev ?EE ?j) <= 255 |- _ => h_d64_bytes_with EL R HNB end
          | h_d64_bytes_with EL HNB HNB ].
  (* [comment removed for export] *)
  Local Ltac h_pref1 c dt PRE EL :=
    replace (c + 1) with (c + Z.of_nat 1) by lia;
    eapply (prf2_close_c T c [0] _ 1%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref2 c dt PRE EL :=
    replace (c + 2) with (c + Z.of_nat 2) by lia;
    eapply (prf2_close_c T c [1; 0] _ 2%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref4 c dt PRE EL :=
    replace (c + 4) with (c + Z.of_nat 4) by lia;
    eapply (prf2_close_c T c [3; 2; 1; 0] _ 4%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [2; 1; 0] _ 3); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [2; 1; 0] _ 3); [| lia| lia| lia];
    eapply (prf2_st_nl T c [1; 0] _ 2); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [1; 0] _ 2); [| lia| lia| lia];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  Local Ltac h_pref8 c dt PRE EL :=
    replace (c + 8) with (c + Z.of_nat 8) by lia;
    eapply (prf2_close_c T c [7; 6; 5; 4; 3; 2; 1; 0] _ 8%nat); [| lia| vm_compute; reflexivity];
    eapply (prf2_st_nl T c [6; 5; 4; 3; 2; 1; 0] _ 7); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [6; 5; 4; 3; 2; 1; 0] _ 7); [| lia| lia| lia];
    eapply (prf2_st_nl T c [5; 4; 3; 2; 1; 0] _ 6); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [5; 4; 3; 2; 1; 0] _ 6); [| lia| lia| lia];
    eapply (prf2_st_nl T c [4; 3; 2; 1; 0] _ 5); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [4; 3; 2; 1; 0] _ 5); [| lia| lia| lia];
    eapply (prf2_st_nl T c [3; 2; 1; 0] _ 4); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [3; 2; 1; 0] _ 4); [| lia| lia| lia];
    eapply (prf2_st_nl T c [2; 1; 0] _ 3); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [2; 1; 0] _ 3); [| lia| lia| lia];
    eapply (prf2_st_nl T c [1; 0] _ 2); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [1; 0] _ 2); [| lia| lia| lia];
    eapply (prf2_st_nl T c [0] _ 1); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [0] _ 1); [| lia| lia| lia];
    eapply (prf2_st_nl T c [] _ 0); [| lia| lia| lia| rewrite !Zupd_length; lia| clear - HNB HT; lia| clear - EL; lia];
    eapply (prf2_st_sq T c [] dt 0); [apply x2prf_open; exact PRE| lia| lia| lia].
  (* [comment removed for export] *)
  Local Ltac h_block L c dt PRE EL DTC DTLEN DTBY :=
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) =>
      let P' := fresh "PRE'" in let L' := fresh "DTLEN'" in let B' := fresh "DTBY'" in
      assert (P' : x2pref T (c + L) d) by (lazymatch L with 1 => h_pref1 c dt PRE EL | 2 => h_pref2 c dt PRE EL | 4 => h_pref4 c dt PRE EL | 8 => h_pref8 c dt PRE EL end);
      assert (L' : zlen d = 16388) by (rewrite !Zupd_length2; exact DTLEN);
      assert (B' : Forall isbyte d) by (repeat (apply Forall_Zupd; [| first [clear; lia| clear - HNB HT EL; lia| assumption| apply Z.mod_pos_bound; clear; lia]]); exact DTBY)
    end.

  (* [comment removed for export] *)
  Lemma rdn_sh0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
    rdn bsegs m (wa (shad p)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof. intros m X n p U Hp Hg. cbn [rdn]. rewrite (unp_shadow_zero m X n p U Hp Hg). reflexivity. Qed.

  Notation LEN := (2 ^ (T - nb)) (only parsing).
  Notation STRET mm r1 r5 r6 r7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 r28 r29 r30 r31 :=
    (STH 0x97990 mm r1 r5 r6 r7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs9 xs10 xs11 r28 r29 r30 r31) (only parsing).
  Notation KRET c := (forall m2 (dt' : list Z) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31,
      XHs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 dt' m2 -> x2pref T c dt' ->
      evtF bsegs RNG POST (STRET m2 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31)) (only parsing).
  Notation STE pc mm len xa3 xa4 :=
    (STH pc mm x1 x5 x6 x7 (Z_to_bv 64 nb) (Z_to_bv 64 (4 * pos)) (Z_to_bv 64 len) xa3 xa4 x15 (Z_to_bv 64 bg) x17
         x18 (Z_to_bv 64 (SYM + bg)) x20 x21 x22 x23 (Z_to_bv 64 pos) x26 x27 x28 x29 x30 x31) (only parsing).

  (* [comment removed for export] *)
  Lemma x2h_retB : forall m2 (dt' : list Z) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31,
    XHs w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 dt' m2 -> x2pref T (pos + LEN * cnt) dt' ->
    evtF bsegs RNG (x2h_postA1 x2 gp tp x8 F fc SPA DT T m0 (pos + LEN * cnt))
         (STRET m2 r1 r5 r6 r7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys9 ys10 ys11 r28 r29 r30 r31).
  Proof.
    intros until r31; intros I PRE. open_xh I.
    apply evtF_done. unfold x2h_postA1, x2h_postA.
    do 37 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact DTC|]. split; [exact DTLEN|]. split; [exact DTBY|]. split; [exact PRE|].
    unfold X2HSC. exact FR.
  Qed.

  (* [comment removed for export] *)
  Lemma x2h_bodyB : forall (dt : list Z),
    u8arr bsegs m0 DT (map (Z_to_bv 8) dt) -> zlen dt = 16388 -> Forall isbyte dt -> bytes_at bsegs m0 SYM syb -> zlen syb = 256 ->
    rw_cells bsegs m0 (SPA + 624) (X2HSC v0 v1 v2 v3 v4 v5 v6 v7 v8 v9) -> mem_inv bsegs m0 -> x2pref T pos dt ->
    KRET (pos + LEN * cnt) ->
    evtF bsegs RNG POST
      (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 SPA) (Z_to_bv 64 nb) x11 (Z_to_bv 64 (T - nb)) x13 x14 x15 (Z_to_bv 64 bg) x17
               x18 x19 x20 x21 x22 x23 (Z_to_bv 64 0x7fff8000) (Z_to_bv 64 pos) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 APX2H) fc None m0 (seg_rom bsegs)).
  Proof.
    intros dt DTC DTLEN DTBY SYB SYLEN FR MI PRE KE. unfold X2HSC in FR.
    assert (MU : munch [(DT + 4, DT + 16388); (SPA + 624, SPA + 704)] m0 m0) by apply munch_refl. assert (WM : wmono bsegs m0 m0) by apply wmono_refl.
    h_open. h_lens.
    unfold APX2H.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    rewrite (sllw_pow2 (T - nb)) by lia. replace (Z.shiftl pos 2) with (4 * pos) by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4; lia).
    (* [comment removed for export] *)
    assert (L1 : 1 <= LEN <= 4096) by (split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia| change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]).
    assert (CS : T - nb = 0 \/ T - nb = 1 \/ T - nb = 2 \/ T - nb = 3 \/ 4 <= T - nb) by lia.
    destruct CS as [E0 | [E1 | [E2 | [E3 | E4]]]];
      [rewrite E0; change (2 ^ 0) with 1| rewrite E1; change (2 ^ 1) with 2| rewrite E2; change (2 ^ 2) with 4| rewrite E3; change (2 ^ 3) with 8
      | assert (16 <= LEN) by (change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia); set (len := LEN) in *].
    1-4: kx_autoFA (@nil kza) [0x97a5c; 0x97f54; 0x98ef4; 0x991ac; 0x99274] 30%nat KZH
      (@nil (Z * Z)) [(DT, 16388); (SYM, 256); (SPA, 728)].
    5: kx_autoFA (@nil kza) [0x97a5c; 0x97f54; 0x98ef4; 0x991ac; 0x99274] 30%nat
      [KZRange SPA 0x10007fff8000 (2^47 - 728); KZRange DT 0x625000 (2^47 - 16388); KZRange SYM 0x625000 (2^47 - 257);
       KZAlign SPA 16; KZAlign DT 4; KZDisj DT 16388 SPA 728; KZDisj SYM 256 SPA 728; KZDisj DT 16388 SYM 256;
       KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12; KZRange len 16 4096]
      (@nil (Z * Z)) [(DT, 16388); (SYM, 256); (SPA, 728)].
    all: kx_mem. all: kx_tidy_run.
    all: kx_setreg 11 (4 * pos); kx_setreg 19 (SYM + bg).
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x991ac) _ _ _ _) =>
             rewrite E0 in KE; change (2 ^ 0) with 1 in KE; replace (pos + 1 * cnt) with (pos + cnt) in KE by lia;
             eapply (x2h_c1B RNG gp _ F fc m0); try eassumption; close_xh
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97a5c) _ _ _ _) => rewrite E1 in KE; change (2 ^ 1) with 2 in KE; eapply (x2h_c2B RNG gp _ F fc m0); try eassumption; close_xh
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x99274) _ _ _ _) => rewrite E2 in KE; change (2 ^ 2) with 4 in KE; eapply (x2h_c4B RNG gp _ F fc m0); try eassumption; close_xh
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x97f54) _ _ _ _) => rewrite E3 in KE; change (2 ^ 3) with 8 in KE; eapply (x2h_c8B RNG gp _ F fc m0); try eassumption; close_xh
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x98ef4) _ _ _ _) => eapply (x2h_cdB RNG gp _ F fc m0); try eassumption; close_xh
         end.
  Qed.

End H.
End CANSEC1.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Theorem x2h_proofA1 : x2h_stmtA1.
Proof.
  intros RNG x1 x2 gp tp x5 x6 x7 x8 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 F fc m SPA DT SYM pos cnt bg nb T dt syb.
  intros HY MI DTC DTLEN DTBY SYB SYLEN ART UDT USY TP HPOS HBG HCNT HBC HNB HT HROOM PRE SL FR.
  eapply (x2h_bodyB RNG gp tp F fc m SPA DT SYM x2 x8 x1 x5 x6 x7 x11 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31
            v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 syb pos cnt bg nb T HY UDT USY ART HPOS HBG HCNT HBC HNB HT HROOM SL _ dt DTC DTLEN DTBY SYB SYLEN FR MI PRE).
  intros until r31; intros I PRE2.
  eapply x2h_retB; eassumption.
Qed.
End CANSEC2.
