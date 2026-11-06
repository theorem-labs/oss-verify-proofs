(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2 ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF KXUb KXUb2.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AProg_kit AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x2_kit AZ_hft_x2h_defs.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : amem) (SPF DT SYM : Z).
  Variables (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word).     (* [comment removed for export] *)
  Variables (x7 x28 x29 x30 x31 : word).                                    (* [comment removed for export] *)
  Variable syb : list byte.
  Variables (pos cnt bg nb T bs : Z).
  Hypothesis HY : x2hA_hyps RNG SPF DT SYM.
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
  Hypothesis HBS : 0 <= bs < 256.
  Hypothesis HROOM : pos + 2^(T - nb) * cnt <= 4096.
  Variable lvl : Z.
  Hypothesis HL : lvl = 1 \/ lvl = 2.
  Variable POST : machine_state -> Prop.
  (* [comment removed for export] *)
  Local Ltac kx_lia_bf :=
    lazymatch goal with
    | |- context [_ + _ <= _ \/ _] => first [ kx_sep_unhide5 DT SYM SPF SPF SPF; lia | lia | kx_bv_ranges; lia ]
    | |- _ => first [ lia | kx_bv_ranges; lia ]
    end.
  Local Ltac kx_lia ::= kx_lia_bf.
  Local Ltac kxl_lia ::= kx_lia_bf.
  Local Ltac kxa_unpZ ::=
    lazymatch goal with
    | |- unpZ ?mm ?lo1 ?hi1 =>
        first [ kxa_hyp
              | let X := kxk_sbase5 DT SYM SPF SPF SPF lo1 in
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
                let X := kxk_sbase5 DT SYM SPF SPF SPF A in
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
        first [ let X := kxk_sbase5 DT SYM SPF SPF SPF A in
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
    lazymatch goal with
    | MU : munch _ m0 ?m2 |- _ =>
        pose proof (x2h_unp_dtM _ _ _ _ _ HY UDT m2 MU) as UDT1;
        pose proof (x2h_unp_syM _ _ _ _ _ HY USY m2 MU) as USY1;
        try lazymatch goal with WM : wmono _ m0 m2 |- _ => pose proof (x2h_artM _ _ _ _ _ HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac h_open :=
    open_hyh HY; unfold KHIGH in *;
    pose proof (x2h_bands _ _ _ _ HY) as (BDT & BSY & BSP & BSP2 & B5 & B6 & B7 & B8);
    hide_all_disj; unfold hidden in HL; h_reunp.
  (* [comment removed for export] *)
  Notation KZH := [KZRange SPF (0x10007fff8000 + 112) (2^47 - 16); KZRange DT 0x629000 (2^47 - 16388); KZRange SYM 0x629000 (2^47 - 257);
     KZAlign SPF 16; KZAlign DT 4; KZDisj DT 16388 (SPF - 112) 112; KZDisj SYM 256 (SPF - 112) 112; KZDisj DT 16388 SYM 256;
     KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12; KZRange bs 0 255] (only parsing).
  Notation AKH := [KAUnp DT 16388; KAApp DT 16388; KAUnp SYM 256; KAApp SYM 256] (only parsing).
  (* [comment removed for export] *)
  Notation STH pc mm x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPF + -112)) gp tp (Z_to_bv 64 0x7fff8000) x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Notation XHm j0 dt mm := (XH SPF DT SYM m0 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 syb j0 dt mm) (only parsing).

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
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT HBS EL HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 65536 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = lvl) by (rewrite E, EL; clear - R HNB HT HBS HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT HBS EL HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (?v = (?P mod 2 ^ 64 / 281474976710656 / 256) mod 256) |- _ =>
        unfold hidden in E; let H := fresh "KV" in assert (H : v = lvl) by (rewrite E, EL; clear - R HNB HT HBS HD; rewrite (Z.mod_small _ (2^64)) by lia; Z.div_mod_to_equations; lia); clear E
    | E : hidden (_ = ((4294967297 * Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64)) mod 2 ^ 64 / 65536) mod 256) |- _ =>
        x2d_use nb bs sq HBS R
    | E : hidden (_ = (Z.lor (?B mod 2 ^ 64) (?A mod 2 ^ 64) / 65536) mod 256) |- _ =>
        x2w_use nb bs sq HBS R
    | E : hidden (?v = ?X mod 256) |- _ =>
        lazymatch X with
        | context [ev _ _] => fail | context [edenot _ _] => fail
        | context [4294967297] => unfold hidden in E; subst v      (* [comment removed for export] *)
        | context [nb] =>
          unfold hidden in E;
          first [ let H := fresh "KV" in assert (H : v = nb) by (rewrite E; clear - R HNB HT HBS EL; Z.div_mod_to_equations; lia); clear E
                | let H := fresh "KV" in assert (H : v = lvl) by (rewrite E, EL; clear - R HNB HT HBS; Z.div_mod_to_equations; lia); clear E
                | subst v ]
        end
    end;
    repeat match goal with H : ?v = nb |- _ => is_var v; subst v | H : ?v = lvl |- _ => is_var v; subst v end.
  (* [comment removed for export] *)
  Local Ltac h_d64_bytes EL :=
    first [ match goal with R : 0 <= bv_unsigned (ev ?EE ?j) <= 255 |- _ => h_d64_bytes_with EL R HNB end
          | h_d64_bytes_with EL HBS HNB ].
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
  (* [comment removed for export] *)
  Notation STDS mm k c xa3 xa4 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 :=
    (STH 0xa4e6c mm (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 (4 * LEN)) (Z_to_bv 64 18446744073709551615)
        (Z_to_bv 64 (DT + 4 + 4 * c)) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + bg + cnt)) xa3 xa4
        (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 1) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 18446744073709551583) (Z_to_bv 64 (65536 * nb + 16777216 * lvl)) (Z_to_bv 64 (4 * LEN)))
    (only parsing).
  Notation STRET mm x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (STH 0xa5430 mm x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31) (only parsing).
  Notation STE pc mm len xa7 :=
    (STH pc mm (Z_to_bv 64 3) x7 x8 x9 (Z_to_bv 64 (DT + 4 + 4 * pos)) (Z_to_bv 64 (SYM + bg)) (Z_to_bv 64 (SYM + bg + cnt)) (Z_to_bv 64 nb) (Z_to_bv 64 len)
        (Z_to_bv 64 bs) (Z_to_bv 64 lvl) xa7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (only parsing).

  (* [comment removed for export] *)
  Notation STDI mm k c o cc qcc dv xa3 xa4 xs10 xs11 :=
    (STH 0xa4ecc mm (Z_to_bv 64 18446744073709551607) (Z_to_bv 64 18446744073709551599) (Z_to_bv 64 (4 * LEN)) (Z_to_bv 64 18446744073709551615)
        (Z_to_bv 64 (DT + 4 + 4 * cc - o)) (Z_to_bv 64 (SYM + bg + k)) (Z_to_bv 64 (SYM + bg + cnt)) xa3 xa4
        (Z_to_bv 64 bs) (Z_to_bv 64 lvl) (Z_to_bv 64 1) (Z_to_bv 64 o) (Z_to_bv 64 (DT + 4 + 4 * cc - o + 4 * LEN)) (Z_to_bv 64 0)
        (Z_to_bv 64 (2147450880 + qcc)) (Z_to_bv 64 dv) (Z_to_bv 64 (dv mod 2 ^ 64 / 281474976710656)) (Z_to_bv 64 (dv mod 2 ^ 64 / 4294967296))
        (Z_to_bv 64 (dv mod 2 ^ 64 / 65536)) xs10 xs11
        (Z_to_bv 64 18446744073709551591) (Z_to_bv 64 18446744073709551583) (Z_to_bv 64 (65536 * nb + 16777216 * lvl)) (Z_to_bv 64 (4 * LEN)))
    (only parsing).

  Lemma len_bounds : 4 <= T - nb -> 16 <= LEN <= 4096.
  Proof. intros HE. split; [change 16 with (2 ^ 4); apply Z.pow_le_mono_r; lia| change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]. Qed.
  Lemma len_mult16 : 4 <= T - nb -> exists q, LEN = 16 * q.
  Proof. intros HE. exists (2 ^ (T - nb - 4)). change 16 with (2 ^ 4). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
  Lemma blk_room : forall k, 4 <= T - nb -> 0 <= k < cnt -> 0 <= pos + LEN * k /\ pos + LEN * k + LEN <= 4096.
  Proof. intros k HE HK. pose proof (len_bounds HE). pose proof HROOM. nia. Qed.

  (* [comment removed for export] *)
  Lemma x2h_cd_inB : forall m1 (j0 : list byte) (dt : list Z) (k c r o cc qcc dv sq : Z) xa3 xa4 xs10 xs11,
    XHm j0 dt m1 -> 4 <= T - nb -> 0 <= k < cnt -> c = pos + LEN * k -> 0 <= r -> 8 * (r + 1) <= LEN -> o = 32 * r -> cc = c + 8 * r -> qcc = (DT + 4 + 4 * cc) / 8 ->
    dv = 4294967297 * (65536 * nb + 16777216 * lvl + sq) -> 0 <= sq < 65536 -> x2pref T cc dt ->
    (forall m2 (dt' : list Z) (qcc' : Z) ya3 ya4 ys10 ys11, 8 * (r + 2) <= LEN ->
       XHm j0 dt' m2 -> qcc' = (DT + 4 + 4 * (cc + 8)) / 8 -> x2pref T (cc + 8) dt' ->
       evtF bsegs RNG POST (STDI m2 k c (o + 32) (cc + 8) qcc' dv ya3 ya4 ys10 ys11)) ->
    (forall m2 (dt' : list Z) ya3 ya4 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11, 8 * (r + 1) = LEN -> k + 1 < cnt ->
       XHm j0 dt' m2 -> x2pref T (c + LEN) dt' ->
       evtF bsegs RNG POST (STDS m2 (k + 1) (c + LEN) ya3 ya4 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11)) ->
    (forall m2 (dt' : list Z) y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31, 8 * (r + 1) = LEN -> k + 1 = cnt ->
       XHm j0 dt' m2 -> x2pref T (pos + LEN * cnt) dt' ->
       evtF bsegs RNG POST (STRET m2 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STDI m1 k c o cc qcc dv xa3 xa4 xs10 xs11).
  Proof.
    intros until xs11; intros I HE HK HC HR H8 HO HCC HQ HD HSQ PRE KI KS KE. open_xh I. h_open. h_lens. subst o.
    pose proof (len_bounds HE) as L16. destruct (len_mult16 HE) as [lq HLQ]. pose proof (blk_room k HE HK) as BR. rewrite <- HC in BR.
    assert (CR : 0 <= cc /\ cc + 8 <= 4096) by (subst cc; lia).
    assert (QR : 0 <= qcc < 17592186044416) by (subst qcc; Z.div_mod_to_equations; lia).
    assert (DR : 0 <= dv < 2^64) by (rewrite HD; destruct HL as [EL|EL]; rewrite EL; lia).
    set (len := LEN) in *.
    destruct HL as [EL|EL]; rewrite EL; rewrite EL in KI, KS, HD.
    all: kx_autoFA AKH [0xa4ecc; 0xa4e6c; 0xa5430] 80%nat
      [KZRange SPF (0x10007fff8000 + 112) (2^47 - 16); KZRange DT 0x629000 (2^47 - 16388); KZRange SYM 0x629000 (2^47 - 257);
       KZAlign SPF 16; KZAlign DT 4; KZDisj DT 16388 (SPF - 112) 112; KZDisj SYM 256 (SPF - 112) 112; KZDisj DT 16388 SYM 256;
       KZRange pos 0 4096; KZRange bg 0 256; KZRange cnt 0 256; KZRange (bg + cnt) 0 256; KZRange nb 0 12; KZRange T 1 12; KZRange bs 0 255;
       KZRange k 0 255; KZRange (bg + k) 0 255; KZRange cc 0 4088; KZRange r 0 511; KZRange len 16 4096; KZRange (cc - 8 * r + len) 0 4096; KZRange (len - 8 * r) 8 4096;
       KZRange qcc 0 17592186044415; KZWord (2147450880 + qcc) 1%nat 0; KZRange dv 0 (2^64 - 1); KZWr (DT + 4) 16384]
      (@nil (Z * Z)) [(DT, 16388); (SYM, 256); (SPF - 112, 112)].
    all: try (split; [lia| split; [lia| split; [lia|]]];
              replace (2147450880 + qcc) with (shad (DT + 4 + 4 * cc)) by (rewrite shad_div; unfold ASHOFF; subst qcc; Z.div_mod_to_equations; lia);
              apply (rdn_sh0 m1 DT 16388); [exact UDT1| lia| Z.div_mod_to_equations; lia]).
    all: try lazymatch goal with
         | |- accP _ _ _ => pose proof RSDT as RSDTn; unfold shspan in RSDTn; rewrite !shad_div in RSDTn; unfold ASHOFF in RSDTn; kx_acc RSDTn
         end.
    all: kxk_keepg DTC. all: kx_mem. all: h_d64_bytes_with EL HSQ HD. all: kxv_reveal. all: kx_tidy_run. all: clear KXUL0.
    all: h_block 8 cc dt PRE EL DTC DTLEN DTBY.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa4ecc) _ _ _ _) =>
             kx_setreg 10 (DT + 4 + 4 * (cc + 8) - (32 * r + 32)); kx_setreg 19 (DT + 4 + 4 * (cc + 8) - (32 * r + 32) + 4 * len);
             replace (qcc + 2147450884) with (2147450880 + (qcc + 4)) by lia;
             eapply KI; [lia| close_xh| subst qcc; Z.div_mod_to_equations; lia| exact PRE']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa4e6c) _ _ _ _) =>
             kx_setreg 10 (DT + 4 + 4 * (c + len)); kx_setreg 11 (SYM + bg + (k + 1));
             replace (cc + 8) with (c + len) in PRE' by lia;
             eapply KS; [lia| lia| close_xh| exact PRE']
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0xa5430) _ _ _ _) =>
             replace (cc + 8) with (pos + len * cnt) in PRE' by (subst cc c; replace cnt with (k + 1) by lia; lia);
             eapply KE; [lia| lia| close_xh| exact PRE']
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2h_cd_inloopB : forall (f : nat) m1 (j0 : list byte) (dt : list Z) (k c r o cc qcc dv sq : Z) xa3 xa4 xs10 xs11,
    XHm j0 dt m1 -> 4 <= T - nb -> 0 <= k < cnt -> c = pos + LEN * k -> 0 <= r -> 8 * (r + 1) <= LEN -> LEN - 8 * r <= 8 * Z.of_nat f -> o = 32 * r ->
    cc = c + 8 * r -> qcc = (DT + 4 + 4 * cc) / 8 -> dv = 4294967297 * (65536 * nb + 16777216 * lvl + sq) -> 0 <= sq < 65536 -> x2pref T cc dt ->
    (forall m2 (dt' : list Z) ya3 ya4 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11, k + 1 < cnt ->
       XHm j0 dt' m2 -> x2pref T (c + LEN) dt' ->
       evtF bsegs RNG POST (STDS m2 (k + 1) (c + LEN) ya3 ya4 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11)) ->
    (forall m2 (dt' : list Z) y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31, k + 1 = cnt ->
       XHm j0 dt' m2 -> x2pref T (pos + LEN * cnt) dt' ->
       evtF bsegs RNG POST (STRET m2 y6 y7 ys0 ys1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y28 y29 y30 y31)) ->
    evtF bsegs RNG POST (STDI m1 k c o cc qcc dv xa3 xa4 xs10 xs11).
  Proof.
    induction f as [|f IH]; intros until xs11; intros I HE HK HC HR H8 HF HO HCC HQ HD HSQ PRE KS KE; [lia|].
    eapply x2h_cd_inB; [exact I| exact HE| exact HK| exact HC| exact HR| exact H8| exact HO| exact HCC| exact HQ| exact HD| exact HSQ| exact PRE| | |].
    - intros m2 dt' qcc' ya3 ya4 ys10 ys11 H82 I2 HQ' PRE2.
      eapply (IH _ _ _ k c (r + 1) (o + 32) (cc + 8) qcc' dv sq); [exact I2| exact HE| exact HK| exact HC| lia| lia| lia| lia| lia| exact HQ'| exact HD| exact HSQ| exact PRE2| exact KS| exact KE].
    - intros until ys11; intros H81 HK1 I2 PRE2. eapply KS; [exact HK1| exact I2| exact PRE2].
    - intros until y31; intros H81 HK1 I2 PRE2. eapply KE; [exact HK1| exact I2| exact PRE2].
  Qed.


End H.
End CANSEC1.
