(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_kit2 Sj_num_fc_defs Sj_num_fc_defs2 Sj_num_fc_q1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Local Ltac akstep ::=
  zstep; nnorm; kb2z; anorm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (Z_to_le_bytes ?n ?z)) _) =>
      lazymatch n with
      | 8%nat => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
      | 4%nat => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
      | 2%nat => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
      | 1%nat => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z))
      end;
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]; mem_after_store
  | |- _ => idtac
  end.

Ltac akwalk_abs PCS K :=
  akwalk ltac:(fun pc => first [ K pc | (lazymatch PCS with context [pc] => idtac end; num_abstract_loads; num_abstract_data; akstep; akwalk_abs PCS K) ]).

Section FCA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq f A FIRST LAST OUT : Z) (txt : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 192 - d)%Z.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x66b000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + TL)%Z.
  Hypothesis TSEP : ((A + TL <= f \/ f + 1024 <= A) /\ (A + TL <= S \/ S + 128 <= A))%Z.
  Hypothesis OUTR : (OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP)%Z.

  Notation W := [(lo, spq + 88); (f + 32, f + 536); (f + 608, f + 680); (f / 8 + 2147450884, f / 8 + 2147450947); (OUT, OUT + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (FIRST / 8)) (LAST - 8 * (FIRST / 8)).
  Hypothesis SHPO : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' OUT 8.
  Variable Q : machine_state -> Prop.
  Collection FCH := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO.

  Notation FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Notation FCP pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (f + 608)) xs6 (Z_to_bv 64 LAST) xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Notation tb := (ftb A txt).
  Notation ge48 := (fge48 A txt).
  Notation FCPINV := (fc_pinv spq f A OUT lo txt m0).

  Notation ERRA_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm ->
     evt asegs Q (FCP 0x66b4c (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Notation ERRB_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
     evt asegs Q (FCP 0x66b4c (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Hypothesis KERRA : forall ra1, In ra1 FC_ERRA -> ERRA_K ra1.
  Hypothesis KERRB : forall ra1, In ra1 FC_ERRB -> ERRB_K ra1.

  Ltac fc_in_list := unfold FC_ERRA, FC_ERRB; cbn [In]; repeat (first [left; reflexivity | right]).
  Ltac fc_erra_cut := eapply evt_eq; [| eapply KERRA]; [num_st_eq | fc_in_list | fc_pclose].
  Ltac fc_errb_cut := eapply evt_eq; [| eapply KERRB]; [num_st_eq | fc_in_list | fc_pclose].

  Notation FCD D := (D sp gp tp F fc lo spq f A FIRST LAST OUT txt m0 Q) (only parsing).
  Notation FCL L := (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q) (only parsing).

  Ltac fc_env :=
    destruct SPQ as [Hd Hspq]; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8.

  Hypothesis FRM0 : frm0 fc.
  Hypothesis SHPL1 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x288a0 10416.
  Hypothesis SHPL2 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2b220 640.
  Collection FCH2 := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO SHPL1 SHPL2.
  Notation FCS2 pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom asegs)).
  Notation FCINV2 := (fc_inv2 spq f A OUT lo txt m0).

  Notation FCL2 L := (L sp gp tp lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q SHPL1 SHPL2) (only parsing).

  Notation PF := (fpfacts A txt FIRST LAST).

  Definition fc_47c_k : Prop :=
    forall (q IP IL FPT FL : Z) (ww : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
           c0 c8 c16 c24 c32 c40 c64 c80 lmw negb vb tmb errw (mm : mem),
      FCINV2 c0 c8 c16 c24 c32 c40 c64 c80 (Z_to_bv 64 q) ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
      PF IP IL FPT FL -> (-342 <= q <= 308)%Z ->
      evt asegs Q (FCS2 0xc8148 xra xt0 xt1 xt2 xa0 ww xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                        (Z_to_bv 64 q) xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Section CERR.
  Hypothesis K7F4 : fc_7f4_k sp gp tp lo spq f A OUT txt m0 Q.
  Hypothesis K47C : fc_47c_k.

  Definition fcq_k (pc : Z) : Prop :=
    forall (q IP IL FPT FL : Z) (ww : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
           c0 c8 c16 c24 c32 c40 c64 c80 lmw negb vb tmb errw (mm : mem),
      FCINV2 c0 c8 c16 c24 c32 c40 c64 c80 (Z_to_bv 64 q) ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
      PF IP IL FPT FL -> (-342 <= q <= 308)%Z ->
      evt asegs Q (FCS2 pc xra xt0 xt1 xt2 xa0 ww xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                        (Z_to_bv 64 q) xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Ltac num_mark_words :=
    repeat match goal with
    | x : word |- _ => lazymatch goal with _ : IsData x |- _ => fail | _ => idtac end; let M := fresh "DM" in assert (M : IsData x) by exact I
    end.
  Ltac cf_tables mm :=
    let p5t := fresh "p5t" in let P5L := fresh "P5L" in let P5T := fresh "P5T" in let P5Z := fresh "P5Z" in
    destruct (image_readable_b asegs mm (Z.to_nat 10416) 0x288a0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (p5t & P5L & P5T);
    assert (P5Z : Z.of_nat (length p5t) = 10416%Z) by (rewrite P5L; apply Z2Nat.id; lia); clear P5L.
  Ltac fcq_start :=
    unfold fcq_k; intros until mm; intros INV FRM PFp Hq;
    lazymatch goal with INVh : fc_inv2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m |- _ =>
      let INV0 := fresh "INV0" in pose proof INVh as INV0; fc_open2 INV0; fc_env; cf_tables m end;
    num_mark_words.
  Ltac cut7a4 INV := first [ eapply evt_eq; [| eapply (FCL2 fc_7a4 K7F4)]; [num_st_eq | exact INV | assumption] | fail 100 "cut 7a4" ].
  Ltac cutq K q IP IL FPT FL ww INV PFp := first [ eapply evt_eq; [| eapply (K q IP IL FPT FL ww)]; [num_st_eq | exact INV | assumption | exact PFp | lia] | fail 100 "cut" ].

  Lemma fcq_47c : fcq_k 0xc8148.
  Proof using FCH2 K47C. unfold fcq_k. intros. eapply K47C; eassumption. Qed.

  Lemma fcq_440 : fcq_k 0xc810c.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc8470%Z => cut7a4 INV
      | 0xc8148%Z => cutq fcq_47c q IP IL FPT FL ww INV PFp
      end).
  Qed.

  Lemma fcq_328 : fcq_k 0xc7ff4.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc810c%Z => cutq fcq_440 q IP IL FPT FL ww INV PFp
      end).
  Qed.

  Lemma fc_320 : forall (q IP IL FPT FL : Z) (ww : word) xra xt0 xt1 xt2 (xa0 : word) xa2 (xa3 : word) xa4 xa5 xa6 xa7 xs6 (xs7 xs11 : word) xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 lmw negb vb tmb errw (mm : mem),
    FCINV2 c0 c8 c16 c24 c32 c40 c64 c80 (Z_to_bv 64 q) ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
    PF IP IL FPT FL -> ((-342 <= q <= 308)%Z \/ (xs7 = xa3 /\ xs11 = xa0)) ->
    evt asegs Q (FCS2 0xc7fec xra xt0 xt1 xt2 xa0 ww xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 q) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 K7F4 K47C.
    intros until mm. intros INV FRM PFp [Hq | [E1 E2]].
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xc8470%Z => cut7a4 INV
        | 0xc7ff4%Z => cutq fcq_328 q IP IL FPT FL ww INV PFp
        end).
    - subst xa3 xa0.
      awalk ltac:(fun pc => lazymatch pc with
        | 0xc8470%Z => cut7a4 INV
        end).
  Qed.

  Lemma fcq_320 : fcq_k 0xc7fec.
  Proof using FCH2 K7F4 K47C.
    unfold fcq_k. intros until mm. intros INV FRM PFp Hq.
    eapply (fc_320 q IP IL FPT FL ww); [exact INV | exact FRM | exact PFp | left; lia].
  Qed.
  Lemma fcq_25c : fcq_k 0xc7f28.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with | 0xc7fec%Z => cutq fcq_320 q IP IL FPT FL ww INV PFp end).
  Qed.
  Lemma fcq_224 : fcq_k 0xc7ef0.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with | 0xc7f28%Z => cutq fcq_25c q IP IL FPT FL ww INV PFp | 0xc7fec%Z => cutq fcq_320 q IP IL FPT FL ww INV PFp end).
  Qed.
  Lemma fcq_28c : fcq_k 0xc7f58.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with | 0xc7fec%Z => cutq fcq_320 q IP IL FPT FL ww INV PFp end).
  Qed.
  Lemma fcq_1c8 : fcq_k 0xc7e94.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with
      | 0xc7ef0%Z => cutq fcq_224 q IP IL FPT FL ww INV PFp
      | 0xc7f58%Z => cutq fcq_28c q IP IL FPT FL ww INV PFp
      | 0xc7fec%Z => cutq fcq_320 q IP IL FPT FL ww INV PFp
      end).
  Qed.
  Lemma fcq_0a8 : fcq_k 0xc7d74.
  Proof using FCH2 K7F4 K47C.
    fcq_start. astep.
    awalk ltac:(fun pc => lazymatch pc with | 0xc7e94%Z => cutq fcq_1c8 q IP IL FPT FL ww INV PFp end).
  Qed.

  Definition cf1_out (q : Z) (w s7v s11v : word) : Prop :=
    (-342 <= q <= 308)%Z \/ (q < -342 /\ s7v = Z_to_bv 64 0 /\ s11v = Z_to_bv 64 0)%Z \/
    (308 < q /\ s7v = Z_to_bv 64 0 /\ s11v = Z_to_bv 64 2047)%Z \/ (bv_unsigned w = 0)%Z.

  Lemma fc_074 : forall (q IP IL FPT FL : Z) (ww : word) xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 (xs7 xs11 : word) xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 c80 lmw negb vb tmb errw (mm : mem),
    FCINV2 c0 c8 c16 c24 c32 c40 c64 c80 (Z_to_bv 64 q) ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
    PF IP IL FPT FL -> (-9223372036854775808 <= q < 9223372036854775808)%Z -> (1 <= bv_unsigned ww <= 18446744073709551614)%Z ->
    cf1_out q ww xs7 xs11 ->
    evt asegs Q (FCS2 0xc7d40 xra xt0 xt1 xt2 xa0 ww xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 OUT) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 q) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 K7F4 K47C.
    intros until mm. intros INV FRM PFp Hq HW R.
    assert (W1 : ((bv_unsigned ww + 1) mod 18446744073709551616 = bv_unsigned ww + 1)%Z) by (apply Z.mod_small; lia).
    destruct R as [R | [(R & -> & ->) | [(R & -> & ->) | R]]]; [ | | | exfalso; lia ].
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xc7d74%Z => cutq fcq_0a8 q IP IL FPT FL ww INV PFp
        | 0xc7fec%Z => first [ eapply evt_eq; [| eapply (fc_320 q IP IL FPT FL ww)]; [num_st_eq | exact INV | assumption | exact PFp | left; lia] | fail 100 "cut" pc ]
        end).
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xc7fec%Z => first [ eapply evt_eq; [| eapply (fc_320 q IP IL FPT FL ww)]; [num_st_eq | exact INV | assumption | exact PFp | right; split; reflexivity] | fail 100 "cut" pc ]
        end).
    - awalk ltac:(fun pc => lazymatch pc with
        | 0xc7fec%Z => first [ eapply evt_eq; [| eapply (fc_320 q IP IL FPT FL ww)]; [num_st_eq | exact INV | assumption | exact PFp | right; split; reflexivity] | fail 100 "cut" pc ]
        end).
  Qed.
  End CERR.
End FCA.
