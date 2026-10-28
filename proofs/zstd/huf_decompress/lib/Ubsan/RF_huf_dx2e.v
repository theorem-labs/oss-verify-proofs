(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_bitinit RF_huf_dx2 RF_huf_dx2b RF_huf_dx2c RF_huf_dx2d.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Ltac dec_if := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let b := eval vm_compute in c in change c with b; cbv iota end.

Ltac zbr := repeat (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail | _ => zstep end).
Ltac ck U := if_cases U; zify_cond U; try (exfalso; lia).

Lemma x2e_cells_app : forall segs m A B cs1 cs2,
  rw_cells segs m A cs1 -> rw_cells segs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A B cs1 cs2 ((WF1 & B1) & W1) ((WF2 & B2) & W2) EB. subst B.
  assert (CB : forall l, cells_bytes (cs1 ++ l) = cells_bytes cs1 ++ cells_bytes l).
  { intros l. clear. induction cs1 as [|c cs IH]; cbn; [reflexivity | rewrite IH, app_assoc; reflexivity]. }
  assert (CS : forall l, cells_size (cs1 ++ l) = (cells_size cs1 + cells_size l)%nat).
  { intros l. clear. induction cs1 as [|c cs IH]; cbn; [reflexivity | rewrite IH; lia]. }
  pose proof (cells_bytes_length cs1 WF1) as L1.
  split; [split |].
  - apply cells_wf_app; split; assumption.
  - rewrite CB. apply bytes_at_app. split; [exact B1 | rewrite L1; exact B2].
  - rewrite CS. unfold wr_at in *. destruct W1 as (A0 & AB1 & WV1), W2 as (A20 & AB2 & WV2).
    rewrite Nat2Z.inj_add. split; [lia | split; [lia |]].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [HL | HG].
    + apply WV1; lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply WV2; lia.
Qed.

Lemma x2e_lhu : forall (a b : byte) c d, 1 <= c <= 12 -> 1 <= d <= 12 ->
  zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat 2) [a; b; Z_to_bv 8 c; Z_to_bv 8 d])))) =
  Z_to_bv 64 (c + 256 * d).
Proof.
  intros a b c d Hc Hd.
  assert (HC : List.In c [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  assert (HD : List.In d [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  cbn [List.In] in HC, HD.
  repeat (destruct HC as [<- | HC]); repeat (destruct HD as [<- | HD]); try contradiction; vm_compute; reflexivity.
Qed.

Lemma x2e_lwu : forall c d, 1 <= c <= 12 -> 1 <= d <= 12 ->
  zext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 (skipn (Z.to_nat 0) [Z_to_bv 8 d; Z_to_bv 8 1; Z_to_bv 8 c; Z_to_bv 8 d])))) =
  Z_to_bv 64 (d + 256 + 65536 * c + 16777216 * d).
Proof.
  intros c d Hc Hd.
  assert (HC : List.In c [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  assert (HD : List.In d [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  cbn [List.In] in HC, HD.
  repeat (destruct HC as [<- | HC]); repeat (destruct HD as [<- | HD]); try contradiction; vm_compute; reflexivity.
Qed.

Lemma x2e_desc : forall tl mtl, 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  Z.shiftr (mtl + 256 + 65536 * tl + 16777216 * mtl) 16 = tl + 256 * mtl
  /\ Z.shiftr (Z.modulo (Z.shiftl (mtl + 256 + 65536 * tl + 16777216 * mtl) 40) 18446744073709551616) 58 = tl / 4.
Proof.
  intros c d Hc Hd.
  assert (HC : List.In c [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  assert (HD : List.In d [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  cbn [List.In] in HC, HD.
  repeat (destruct HC as [<- | HC]); repeat (destruct HD as [<- | HD]); try contradiction; vm_compute; split; reflexivity.
Qed.

Lemma x2e_bw : forall x, 0 <= x < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 x)) = x.
Proof.
  intros x Hx. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section DX2E.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).     (* [comment removed for export] *)
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis DT4 : DT mod 4 = 0.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation D2 l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16) (only parsing).
  Notation XM := (RF_huf_dx2.XM ra sp s0 s1 s2 s3 s4 s5 s6 s7 m0 DST dcap SS DT lo src cbs).
  Notation BDC := (RF_huf_dx2.BDC SS).

  (* [comment removed for export] *)
  Definition ENT (buf : list Z) : Prop :=
    u8arr usegs m0 DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap
    /\ bytes_at usegs m0 SS (map (Z_to_bv 8) src) /\ bytes_at usegs m0 (DT + 4) cbs
    /\ bytes_at usegs m0 DT [Z_to_bv 8 mtl; Z_to_bv 8 1; Z_to_bv 8 tl; Z_to_bv 8 mtl]
    /\ stk usegs m0 lo SP /\ mem_inv usegs m0.

  Ltac x2e_xm FR :=
    unfold RF_huf_dx2.XM;
    lazymatch goal with ARR : u8arr usegs ?m DST (map (Z_to_bv 8) ?bf), LB : zlen ?bf = dcap |- _ =>
      split; [exists bf; split; [exact ARR | exact LB] |] end;
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact FR|];
    repeat (split; [eassumption|]); eassumption.

  Ltac x2e_step1 stops := lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let t := eval vm_compute in (existsb (Z.eqb p) stops) in
        lazymatch t with true => fail | false => zstep end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let U := fresh "U" in if_cases U; zify_cond U;
        try (match goal with D : Z.shiftr (Z.modulo (Z.shiftl _ 40) _) 58 = _ |- _ => rewrite D in U end);
        try (exfalso; lia)
    end.

  Ltac x2e_drv n stops := lazymatch n with
    | O => idtac
    | S ?k => tryif x2e_step1 stops then x2e_drv k stops else idtac
    end.

  Ltac x2e_drive stops := x2e_drv 200%nat stops.

  (* [comment removed for export] *)
  Lemma x2_entry : forall buf (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), ENT buf ->
    evt usegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SS) (Z_to_bv 64 n)
                           (Z_to_bv 64 DT) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 PHUF_DX2_1X) fc None m0 (seg_rom usegs)).
  Proof using All.
    intros buf t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 (ARR & LB & SRCB & CBB & HDR & STK & MI).
    pose proof TOK as (TL & TLEN & TCK). unfold HUF_TABLELOG_MAX in TL.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (MU : munch DW m0 m0) by apply munch_refl. assert (WM : wmono usegs m0 m0) by apply wmono_refl.
    carve_frame 72%nat STK. rename FR into FRS.
    carve_frame 40%nat STK. rename FR into FRB.
    unfold PHUF_DX2_1X.
    zto 0x1a500.
    assert (ESP : bv_unsigned (Z_to_bv 64 (SP + -112)) = SP + -112)
      by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn; lia).
    call (bit_init_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (SP + -112) SS src _ lo).
    all: rewrite ?ESP.
    all: try (first [eassumption | exact BYS | lia | reflexivity | (f_equal; lia)]).
    all: pose proof (init_dstream_ok src) as INI0.
    all: first [pose proof (INI0 (Forall_all_bytes _ BYS)) as INI | pose proof INI0 as INI]; clear INI0.
    all: destruct INI as [(e & EE) | (d & ED & BOK & BZ & SH)].
    all: lazymatch goal with
         | EE : init_dstream src = Err ?e |- _ =>
             lazymatch goal with H : context [match init_dstream src with _ => _ end] |- _ =>
               rewrite EE in H; cbn iota in H; destruct H as (RET & jj & RJ) end;
             pose proof (RF_huf_dx2.x2_init_err src e EE) as ER
         | ED : init_dstream src = Ok ?d |- _ =>
             lazymatch goal with H : context [match init_dstream src with _ => _ end] |- _ =>
               rewrite ED in H; cbn iota in H; destruct H as (RET & BZ2 & jp & RJ) end
         end.
    all: lazymatch type of RET with ?r = _ => subst r end.
    all: rewrite ?ESP in *.
    all: pose proof (x2e_cells_app _ _ _ _ _ _ RJ FRS) as FR; specialize (FR ltac:(cbn [cells_size csize bitd_cells]; lia)).
    all: clear RJ FRS.
    all: zbr.
    all: ck KE.
    all: lazymatch goal with ER : 1 <= _ <= 119 |- _ =>
           zto 0x15484; eapply (D2 RF_huf_dx2.x2_ret); x2e_xm FR | _ => idtac end.
    all: assert (A3 : Z.land DT 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact DT4).
    all: try (unfold bitd_cells in FR; cbn [app] in FR).
    all: x2e_drive [0x14d00; 0x14dd0; 0x149e4; 0x149e8; 0x15150; 0x15484].
    all: lazymatch goal with H : bytes_at usegs ?mc DT _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
           pose proof (bytes_at_read usegs mc DT _ 2 2 H ltac:(lia) ltac:(cbn; lia)) as RDT;
           pose proof (bytes_at_read usegs mc DT _ 0 4 H ltac:(lia) ltac:(cbn; lia)) as RDT4 end.
    all: zstep.
    all: rewrite ?x2e_lwu by lia.
    all: pose proof (x2e_desc tl mtl TL MTL) as (DS1 & DS2).
    all: x2e_drive [0x14d00; 0x14dd0; 0x149b4; 0x15150; 0x15484].
    all: rewrite ?DS1.
    all: try unfold FseNCount.Zlength in SH.
    all: destruct SH as [(L & EP & EB) | (L & EP & EB)].
    all: assert (BW0 : bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bd_bits d))) = bd_bits d) by (apply x2e_bw; lia).
    all: try (replace (sx32 (Z_to_bv 64 (bd_bits d))) with (Z_to_bv 64 (bd_bits d))
                by (unfold sx32; rewrite BW0; reflexivity)).
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14d00) _ _ _ _) =>
             first [ eapply ((D2 RF_huf_dx2d.x2_single) _ (Z_to_bv 64 (bd_cont d)) (Z_to_bv 64 (bd_bits d)) jp (bd_ptr d) (bd_bits d))
                   | assert (E0 : Z_to_bv 64 DST = Z_to_bv 64 (DST + dcap)) by (f_equal; lia);
                     rewrite E0 at 1; clear E0;
                     eapply ((D2 RF_huf_dx2d.x2_single) _ (Z_to_bv 64 (bd_cont d)) (Z_to_bv 64 (bd_bits d)) jp (bd_ptr d) (bd_bits d)) ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14dd0) _ _ _ _) =>
             eapply ((D2 RF_huf_dx2c.x2_l4_entry) _ (Z_to_bv 64 (bd_cont d)) (Z_to_bv 64 (bd_bits d)) jp (bd_ptr d) (bd_bits d))
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x149b4) _ _ _ _) =>
             eapply ((D2 RF_huf_dx2b.x2_l5_entry) _ (Z_to_bv 64 (bd_cont d)) (Z_to_bv 64 (bd_bits d)) jp (bd_ptr d) (bd_bits d))
         end.
    all: first [x2e_xm FR | exact BW0 | lia].
  Qed.

End DX2E.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem dec_1x2_proof : dec1_int_stmt x2_tab PHUF_DX2_1X.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m DST dcap SR DT mtl src jd lo
    MTL TAB HD DC SRCB BYS NSM S16 SP0 DT0 DT8 DTL DL SL DJ1 DJ2 DJ3 STK LOS SP16 MI E0 E1 E2 E3 E4.
  subst a0 a1 a2 a3 a4.
  destruct TAB as (tl & cells & HDR & ZC & TOK & TLE & CBB).
  pose proof TOK as (TL & TLEN & _). unfold HUF_TABLELOG_MAX in TL.
  assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in DTL, DJ1.
  unfold HUF_DEC_STACK in LOS.
  assert (BUF : exists buf, u8arr usegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap).
  { destruct HD as [(-> & ->) | (DP & D8 & RW)].
    - exists []. split; [| reflexivity]. split; [apply bytes_at_nil; lia |].
      unfold wr_at. cbn [map length Z.of_nat]. split; [lia | split; [lia | intros; lia]].
    - exists (map bv_unsigned jd).
      pose proof (proj1 (proj1 RW)) as WF. cbn in WF. destruct WF as (WF & _).
      rewrite map_map, (map_ext _ (fun x => x))
        by (intros; apply bv_eq; rewrite Z_to_bv_unsigned;
            first [apply bv_wrap_bv_unsigned | apply bv_wrap_small, bv_unsigned_in_range]).
      rewrite map_id.
      split; [exact (u8arr_of_rw_cells usegs m DST _ jd RW) | rewrite length_map; lia]. }
  destruct BUF as (buf & ARR & LB).
  eapply (x2_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT mtl tl lo src cells
            (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells))).
  all: try first [ exact ARR | eassumption | reflexivity ].
  all: try (destruct HD as [(? & ?) | (? & ? & ?)]; intros; lia).
  - rewrite length_firstn, x2_bytes'_length. lia.
  - unfold ENT. split; [exact ARR|]. split; [exact LB|]. split; [exact SRCB|]. split; [exact CBB|].
    split; [exact HDR|]. split; [exact STK | exact MI].
Qed.
End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
