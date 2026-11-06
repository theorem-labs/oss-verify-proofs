(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells Step.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_kit AF_kit3 AF_unwind AF_unwind_walk2 AF_free_kit AF_ia AF_realloc1 AF_realloc2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

#[warnings="-notation-for-abbreviation"] Notation IA := 0xaed80.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RG.
Variable P : acc -> Prop.
Variables (gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo p n : Z) (ii : bool) (izl : list byte) (TSD CTX T top bot : Z).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 8192.
Hypothesis SPH : usp < 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HTB : 0 <= bot < top /\ top <= 2^47.
Hypothesis Hp : 0 < p < 2^47.
Hypothesis Hn : 0 < n < 2^64.
Hypothesis EZ : izl = repeat zb0 (Z.to_nat 0x40000).
Hypothesis HTSD : 0x5cfdd0 <= TSD /\ TSD + 8 <= 0x603000.
Hypothesis HCTX : 0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling.
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= 2^64 -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma thread_cells_frame : forall W m m', thread_cells m tp TSD CTX T -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => 0x603000 <= fst iv /\ (snd iv <= CTX + 152 \/ CTX + 160 <= fst iv)) W -> thread_cells m' tp TSD CTX T.
Proof.
  intros W m m' (X1 & X2 & X3 & X4 & X5) MU WM FW.
  assert (D : forall A k, 0 <= A -> (A + Z.of_nat k <= 0x603000 \/ (CTX + 152 <= A /\ A + Z.of_nat k <= CTX + 160)) -> disjoint_from W A (Z.of_nat k)).
  { intros A k HA HB. clear MU. induction FW as [|[u v] W' Hiv FW IH]; [exact I|]. cbn [disjoint_from fst snd] in *. split; [clear -HA HB Hiv; lia| exact IH]. }
  split; [| split; [| split; [| split]]];
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply D; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear -HTSD HCTX HTP; lia]).
Qed.

(* [comment removed for export] *)
Definition preW : list (Z * Z) := [(lo, usp); (IA, IA + 0x81030); (0x13d608, 0x13d60c); (T + 3168, T + 3169); (T + 2856, T + 2872)].

(* [comment removed for export] *)
Definition rpre_post (ra s0 s1 s2 s3 s4 s5 s6 : word) (st5 st6 : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 a6 a7 s4w : word) (m2 : mem) (ws tr : list word) (bpw : word) (j1800 j8 j8b j8c : list byte),
    ms = MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 (usp - 2208)) gp tp t0 t1 t2 (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
                 (Z_to_bv 64 AINST) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                 (Z_to_bv 64 AINST) (Z_to_bv 64 n) s4w (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALLOCATE_FN) fc None m2 (seg_rom asegs)
    /\ munch preW m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp - 2208)
    (* [comment removed for export] *)
    /\ rw_cells asegs m2 0x13d608 [C1 (Z_to_bv 8 1); C1 zb0]
    /\ rw_cells asegs m2 (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]
    /\ u8arr asegs m2 (IA + 8) izl /\ wr_at asegs m2 IA 0x81030
    (* [comment removed for export] *)
    /\ uthread_cells m2 tp TSD CTX T top bot
    /\ rw_cells asegs m2 (T + 2856) [C8 (Z_to_bv 64 (st5 + 1)); C8 (Z_to_bv 64 (st6 + n))]
    (* [comment removed for export] *)
    /\ rw_cells asegs m2 (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C4 (Z_to_bv 64 (Z.of_nat (length tr))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m2 (usp + -2120) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    (* [comment removed for export] *)
    /\ rw_cells asegs m2 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m2 (usp + -1880) [CB 1800 j1800] /\ rw_cells asegs m2 (usp + -80) [C8 bpw] /\ rw_cells asegs m2 (usp + -72) [CB 8 j8]
    /\ rw_cells asegs m2 (usp + -2144) [CB 8 j8b]
    /\ rw_cells asegs m2 (usp + -2160) [CB 8 j8c; C8 (Z_to_bv 64 REA_ASAN_RET)]
    /\ rw_cells asegs m2 (usp - 2208) [C8 s4w; C8 (Z_to_bv 64 REA_PC0); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 usp); C8 (Z_to_bv 64 0x33624)].

Lemma rea_pre : forall (ra s0 s1 s2 s3 s4 s5 s6 t0 t1 a2 a3 a4 a5 a6 a7 : word) (m : mem) (st5 st6 : Z),
  stk asegs m lo usp -> mem_inv asegs m ->
  rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)] ->                                                 (* [comment removed for export] *)
  rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)] -> rw_cells asegs m 0x13d620 [C8 (Z_to_bv 64 4096)] ->   (* [comment removed for export] *)
  rw_cells asegs m 0xae87c [C4 (Z_to_bv 64 30)] ->                                                (* [comment removed for export] *)
  rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)] ->                                         (* [comment removed for export] *)
  rw_cells asegs m 0x13f6ca [C1 (Z_to_bv 8 1)] ->                                                 (* [comment removed for export] *)
  rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0] ->                                       (* [comment removed for export] *)
  wr_at asegs m IA 0x81030 -> u8arr asegs m (IA + 8) izl ->
  (ii = true -> rw_cells asegs m (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]) ->
  uthread_cells m tp TSD CTX T top bot ->
  uanchor asegs m usp ra s0 ->
  rw_cells asegs m (T + 2856) [C8 (Z_to_bv 64 st5); C8 (Z_to_bv 64 st6)] ->                       (* [comment removed for export] *)
  evtA asegs P (rpre_post ra s0 s1 s2 s3 s4 s5 s6 st5 st6 m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REA_ICP) fc None m (seg_rom asegs)).
Proof.
  intros until st6. intros SK MI AI G1 G2 MCS GCF FUM IAF IWR IZ IPV UT UA ST.
  pose proof LOC as LOCu. aceil.
  pose proof HT as [[HTa _] HTb]. pose proof HCTX as [HCa HCb]. aceil.
  eapply (realloc_pro P) with (lo := lo) (ii := ii) (izl := izl) (TSD := TSD) (CTX := CTX) (T := T) (top := top) (bot := bot);
    [exact SK| exact LOC| lia| exact SPH| lia| lia| exact UA| exact MI| lia| lia| exact AI| exact G1| exact G2| exact MCS| exact GCF| exact FUM| exact IAF| exact IWR| exact IZ
    | exact EZ| exact IPV| exact UT| lia| lia| lia| exact (proj2 HCTX)| exact (proj1 HT)| exact (proj2 HT)| exact HTC| lia| exact PSTK| exact PDAT| exact PCTX| exact PT|].
  intros m1 t0' t1' a3' a4' a5' a6' a7' s4' ws tr j1800 j8 j8b bpw MI1 SK1 WM1 MU1 IAF1 IPV1 IZ1 IWR1 UT1 OBJ ARR LEN FTR LTR HDT FR8 FJ1800 FBP FJ8 FJ8B.
  eapply (asan_rea_pro P gp tp t2 _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ lo LOC _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -2144) p n (usp + -2136));
    [exact SK1| lia| lia| exact MI1| lia| lia| intros; apply PSTK; lia|].
  intros m1b j8c MI1b SK1b WM1b MU1b FRA.
  destruct UT1 as (TC1 & T40 & T8 & TU).
  eapply (rea_A P gp tp t2 _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ lo TSD CTX T LOC ltac:(lia) ltac:(split; [lia| exact (proj2 HCTX)]) HT HTC ltac:(lia) PDAT PCTX PT
            _ _ _ _ _ _ _ _ _ _ _ _ m1b (usp + -2144 - 16) p n (usp + -2136) st5 st6);
    [exact SK1b| lia| lia| clear -SPA; Z.div_mod_to_equations; lia| exact MI1b| lia| lia| lia
    | eapply thread_cells_frame; [exact TC1| exact MU1b| exact WM1b| constructor; [cbn; lia| apply Forall_nil]]
    | eapply rw_cells_transport; [exact ST| exact (munch_trans _ _ _ _ MU1 ltac:(eapply munch_weaken; [| exact MU1b]; intros x; cbn; lia))| eapply wmono_trans; [exact WM1| exact WM1b]| cbn; lia]
    | intros; apply PSTK; lia|].
  intros m2 t0'' t1'' a6'' a7'' MI2 SK2 WM2 MU2 TC2 ST2 FR6.
  apply evtA_done. unfold rpre_post.
  (* [comment removed for export] *)
  assert (MU : munch preW m m2).
  { unfold preW. eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x; cbn; lia|].
    eapply munch_trans; [eapply munch_weaken; [| exact MU1b]; intros x; cbn; lia|]. eapply munch_weaken; [| exact MU2]; intros x; cbn; lia. }
  assert (MU12 : munch [(usp - 2240, usp + -2144); (T + 2856, T + 2872)] m1 m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1b]| eapply munch_weaken; [| exact MU2]]; intros x; cbn; lia. }
  pose proof (wmono_trans _ _ _ _ WM1b WM2) as WM12.
  Ltac xfer12 H MU12 WM12 := eapply rw_cells_transport; [exact H| exact MU12| exact WM12| cbn; lia].
  replace (usp + -2144 - 16 - 48) with (usp - 2208) in * by lia. replace (usp + -2144 - 16) with (usp + -2160) in * by lia.
  exists t0'', t1'', a6'', a7'', s4', m2, ws, tr, bpw, j1800, j8, j8b, j8c.
  split; [reflexivity|]. split; [exact MU|]. split; [exact (wmono_trans _ _ _ _ WM1 WM12)|]. split; [exact MI2|]. split; [exact SK2|].
  split; [xfer12 IAF1 MU12 WM12|]. split; [xfer12 IPV1 MU12 WM12|].
  split; [eapply u8arr_transport; [exact IZ1| exact MU12| exact WM12| rewrite EZ, repeat_length; cbn; lia]|]. split; [eapply wr_at_transport; [exact IWR1| exact WM12]|].
  split; [split; [exact TC2| split; [xfer12 T40 MU12 WM12| split; [xfer12 T8 MU12 WM12| xfer12 TU MU12 WM12]]]|].
  split; [exact ST2|].
  split; [xfer12 OBJ MU12 WM12|]. split; [eapply u64arr_transport; [exact ARR| exact MU12| exact WM12| rewrite LEN; cbn; lia]|].
  split; [exact LEN|]. split; [exact FTR|]. split; [exact LTR|].
  split; [xfer12 FR8 MU12 WM12|]. split; [xfer12 FJ1800 MU12 WM12|]. split; [xfer12 FBP MU12 WM12|]. split; [xfer12 FJ8 MU12 WM12|]. split; [xfer12 FJ8B MU12 WM12|].
  split; [eapply rw_cells_transport; [exact FRA| exact MU2| exact WM2| cbn; lia]|].
  exact FR6.
Qed.

(* [comment removed for export] *)
Definition rmid_post (r oldn : Z) (old rest : list byte) (m3 : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2' a6 a7 t3' t4' t5' t6' : word) (m4 : mem),
    ms = MS (mkR (Z_to_bv 64 REA_DEALLOC_RET) (Z_to_bv 64 (usp - 2208)) gp tp t0 t1 t2' (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
                 (Z_to_bv 64 AINST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 1) a6 a7
                 (Z_to_bv 64 AINST) (Z_to_bv 64 (Z.min n oldn)) (Z_to_bv 64 r) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 DEALLOCATE_FN) fc None m4 (seg_rom asegs)
    /\ mem_inv asegs m4 /\ wmono asegs m3 m4 /\ munch [(r, r + Z.min n oldn)] m3 m4
    /\ rw_cells asegs m4 r [CB (Z.to_nat (Z.min n oldn)) (firstn (Z.to_nat (Z.min n oldn)) old); CB (Z.to_nat (n - Z.min n oldn)) rest]
    /\ bytes_at asegs m4 p old.

Lemma rea_mid : forall (t0 t1 t2e a1 a2 a3 a4 a5 a6 a7 s4 t3e t4e t5e t6e : word) (m : mem) (r oldn : Z) (hb1 : byte) (hid : word) (old junk rest : list byte),
  mem_inv asegs m ->
  p + oldn < 2^64 -> 0 < r -> r + n < 2^64 -> 0 <= oldn < 2^40 ->
  rw_cells asegs m (p + -16) [C1 (Z_to_bv 8 2); C1 hb1; C2 (Z_to_bv 64 (oldn / 2^32)); C4 (Z_to_bv 64 oldn); C8 hid] ->
  rw_cells asegs m GOT_REAL_MEMCPY [C8 (Z_to_bv 64 REAL_MEMCPY_VAR)] -> rw_cells asegs m REAL_MEMCPY_VAR [C8 (Z_to_bv 64 MUSL_MEMCPY)] ->
  bytes_at asegs m p old -> length old = Z.to_nat oldn ->
  rw_cells asegs m r [CB (Z.to_nat (Z.min n oldn)) junk; CB (Z.to_nat (n - Z.min n oldn)) rest] ->
  (p + oldn <= r \/ r + n <= p) ->
  (forall a k, p - 16 <= a -> a + Z.of_nat k <= p + oldn -> P (Z_to_bv 64 a, k)) ->
  (forall a k, r <= a -> a + Z.of_nat k <= r + n -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (rmid_post r oldn old rest m)
    (MS (mkR (Z_to_bv 64 REA_ALLOC_RET) (Z_to_bv 64 (usp - 2208)) gp tp t0 t1 t2e (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
             (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AINST) (Z_to_bv 64 n) s4 (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3e t4e t5e t6e)
        F (Z_to_bv 64 REA_ALLOC_RET) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros MI Hpo Hr Hrn Hon HDR GOTM RMV OLD LOLD NEW SEP PHB PNEW.
  eapply (rea_B P gp tp t2e _ _ s7 s8 s9 s10 s11 t3e t4e t5e t6e F fc _ PDAT);
    [exact MI| lia| exact Hpo| exact Hn| exact Hr| exact Hrn| exact Hon| exact HDR| exact GOTM| exact RMV| exact OLD| exact LOLD| exact NEW| exact SEP| exact PHB| exact PNEW|].
  intros m4 t0' t1' t2' a6' a7' t3' t4' t5' t6' MI4 WM4 MU4 DST OLD4. apply evtA_done. unfold rmid_post.
  exists t0', t1', t2', a6', a7', t3', t4', t5', t6', m4. repeat (split; [first [reflexivity| assumption]|]). exact OLD4.
Qed.

(* [comment removed for export] *)
Definition rsuf_post (ra s0 s1 s2 s3 s4 s5 s6 : word) (a0v a1v : Z) (W : list (Z * Z)) (m5 : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2' a1 a2 a3 a4 a5 a6 a7 t3' t4' t5' t6' : word) (m6 : mem),
    ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2' s0 s1 (Z_to_bv 64 a0v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m6 (seg_rom asegs)
    /\ (a1v <> 0 -> a1 = Z_to_bv 64 a1v)
    /\ mem_inv asegs m6 /\ stk asegs m6 lo usp /\ wmono asegs m5 m6 /\ munch W m5 m6
    /\ (a1v <> 0 -> rw_cells asegs m6 (bv_unsigned tp + -164) [C4 (Z_to_bv 64 a1v)]).

Lemma rea_suf_ok : forall (ra s0 s1 s2 s3 s4 s5 s6 t0 t1 t2e a0 a1 a2 a3 a4 a5 a6 a7 s3e s4w t3e t4e t5e t6e bpw : word) (m : mem) (r : Z)
                          (j8 j8b j8c j1800 : list byte) (ws : list word) (len : Z),
  stk asegs m lo (usp - 2208) -> mem_inv asegs m -> 0 < r < 2^64 ->
  rw_cells asegs m (usp - 2208) [C8 s4w; C8 (Z_to_bv 64 REA_PC0); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 usp); C8 (Z_to_bv 64 0x33624)] ->
  rw_cells asegs m (usp + -2160) [CB 8 j8c; C8 (Z_to_bv 64 REA_ASAN_RET)] ->
  rw_cells asegs m (usp + -2144) [CB 8 j8b] ->
  rw_cells asegs m (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (usp + -2120) ws -> length ws = 30%nat ->
  rw_cells asegs m (usp + -1880) [CB 1800 j1800] -> rw_cells asegs m (usp + -80) [C8 bpw] -> rw_cells asegs m (usp + -72) [CB 8 j8] ->
  rw_cells asegs m (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evtA asegs P (rsuf_post ra s0 s1 s2 s3 s4 s5 s6 r 0 [(usp - 2208, usp)] m)
    (MS (mkR (Z_to_bv 64 REA_DEALLOC_RET) (Z_to_bv 64 (usp - 2208)) gp tp t0 t1 t2e (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 p)
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 AINST) s3e (Z_to_bv 64 r) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3e t4e t5e t6e)
        F (ret_pc (Z_to_bv 64 REA_DEALLOC_RET)) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros SK MI Hr FR6 FRA FJ8B OBJ ARR LEN FJ1800 FBP FJ8 FR8.
  rewrite (ret_pc_even REA_DEALLOC_RET) by (unfold REA_DEALLOC_RET; lia).
  replace (usp - 2208) with (usp + -2160 - 48) in * by lia.
  eapply (rea_epi P gp tp t2e _ _ s7 s8 s9 s10 s11 t3e t4e t5e t6e F fc _ lo LOC); [exact SK| lia| lia| exact MI| exact FR6| intros; apply PSTK; lia|].
  intros m5 MI5 SK5 WM5 MU5.
  rewrite (ret_pc_even 0x33624) by lia.
  apply rea_after_ok; [exact Hr|].
  Ltac xf H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn; lia].
  eapply (rea_ret P gp tp t2e _ _ s7 s8 s9 s10 s11 t3e t4e t5e t6e F fc _ lo LOC); [exact SK5| lia| lia| exact MI5| xf FRA MU5 WM5| xf FJ8B MU5 WM5| xf OBJ MU5 WM5
    | eapply u64arr_transport; [exact ARR| exact MU5| exact WM5| rewrite LEN; cbn; lia]| exact LEN| xf FJ1800 MU5 WM5| xf FBP MU5 WM5| xf FJ8 MU5 WM5| xf FR8 MU5 WM5| intros; apply PSTK; lia|].
  intros m6 MI6 SK6 WM6 MU6. apply evtA_done. unfold rsuf_post.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m6. split; [reflexivity|]. split; [intros X; exfalso; exact (X eq_refl)|].
  split; [exact MI6|]. split; [exact SK6|]. split; [exact (wmono_trans _ _ _ _ WM5 WM6)|].
  split; [| intros X; exfalso; exact (X eq_refl)].
  eapply munch_trans; [eapply munch_weaken; [| exact MU5]| eapply munch_weaken; [| exact MU6]]; intros x; cbn; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition preW0 : list (Z * Z) := [(lo, usp); (IA, IA + 0x81030); (0x13d608, 0x13d60c); (T + 3168, T + 3169)].

Definition rpre0_post (ra s0 s1 s2 s3 s4 s5 s6 : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 a7 s4w : word) (m2 : mem) (ws tr : list word) (bpw : word) (j1800 j8 j8b j8c : list byte),
    ms = MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 (usp - 2160)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n)
                 (Z_to_bv 64 AINST) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (usp + -2136)) a7
                 (Z_to_bv 64 0) (Z_to_bv 64 REA_PC0) s4w (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ALLOCATE_FN) fc None m2 (seg_rom asegs)
    /\ munch preW0 m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp - 2160)
    /\ rw_cells asegs m2 0x13d608 [C1 (Z_to_bv 8 1); C1 zb0]
    /\ rw_cells asegs m2 (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]
    /\ u8arr asegs m2 (IA + 8) izl /\ wr_at asegs m2 IA 0x81030
    /\ uthread_cells m2 tp TSD CTX T top bot
    /\ rw_cells asegs m2 (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C4 (Z_to_bv 64 (Z.of_nat (length tr))); C4 (Z_to_bv 64 0)]
    /\ u64arr asegs m2 (usp + -2120) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    /\ rw_cells asegs m2 (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m2 (usp + -1880) [CB 1800 j1800] /\ rw_cells asegs m2 (usp + -80) [C8 bpw] /\ rw_cells asegs m2 (usp + -72) [CB 8 j8]
    /\ rw_cells asegs m2 (usp + -2144) [CB 8 j8b]
    /\ rw_cells asegs m2 (usp + -2160) [CB 8 j8c; C8 (Z_to_bv 64 REA_ASAN_RET)].

Lemma rea0_pre : forall (ra s0 s1 s2 s3 s4 s5 s6 t0 t1 a2 a3 a4 a5 a6 a7 : word) (m : mem),
  stk asegs m lo usp -> mem_inv asegs m ->
  rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)] -> rw_cells asegs m 0x13d620 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m 0xae87c [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)] ->
  rw_cells asegs m 0x13f6ca [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0x13d608 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0] ->
  wr_at asegs m IA 0x81030 -> u8arr asegs m (IA + 8) izl ->
  (ii = true -> rw_cells asegs m (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]) ->
  uthread_cells m tp TSD CTX T top bot ->
  uanchor asegs m usp ra s0 ->
  evtA asegs P (rpre0_post ra s0 s1 s2 s3 s4 s5 s6 m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REA_ICP) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros SK MI AI G1 G2 MCS GCF FUM IAF IWR IZ IPV UT UA.
  pose proof LOC as LOCu. aceil.
  pose proof HT as [[HTa _] HTb]. pose proof HCTX as [HCa HCb]. aceil.
  eapply (realloc_pro P) with (lo := lo) (ii := ii) (izl := izl) (TSD := TSD) (CTX := CTX) (T := T) (top := top) (bot := bot);
    [exact SK| exact LOC| lia| exact SPH| lia| lia| exact UA| exact MI| lia| lia| exact AI| exact G1| exact G2| exact MCS| exact GCF| exact FUM| exact IAF| exact IWR| exact IZ
    | exact EZ| exact IPV| exact UT| lia| lia| lia| exact (proj2 HCTX)| exact (proj1 HT)| exact (proj2 HT)| exact HTC| lia| exact PSTK| exact PDAT| exact PCTX| exact PT|].
  intros m1 t0' t1' a3' a4' a5' a6' a7' s4' ws tr j1800 j8 j8b bpw MI1 SK1 WM1 MU1 IAF1 IPV1 IZ1 IWR1 UT1 OBJ ARR LEN FTR LTR HDT FR8 FJ1800 FBP FJ8 FJ8B.
  eapply (asan_rea0_pro P gp tp t2 _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ lo LOC _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -2144) n (usp + -2136));
    [exact SK1| lia| lia| exact MI1| lia| lia| intros; apply PSTK; lia|].
  intros m2 j8c MI2 SK2 WM2 MU2 FRA. apply evtA_done. unfold rpre0_post.
  assert (MU : munch preW0 m m2).
  { unfold preW0. eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x; cbn; lia|]. eapply munch_weaken; [| exact MU2]; intros x; cbn; lia. }
  Ltac xfer2 H MU2 WM2 := eapply rw_cells_transport; [exact H| exact MU2| exact WM2| cbn; lia].
  destruct UT1 as (TC1 & T40 & T8 & TU).
  replace (usp + -2144 - 16) with (usp - 2160) in * by lia.
  exists t0', t1', a7', s4', m2, ws, tr, bpw, j1800, j8, j8b, j8c.
  split; [reflexivity|]. split; [exact MU|]. split; [exact (wmono_trans _ _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact SK2|].
  split; [xfer2 IAF1 MU2 WM2|]. split; [xfer2 IPV1 MU2 WM2|].
  split; [eapply u8arr_transport; [exact IZ1| exact MU2| exact WM2| rewrite EZ, repeat_length; cbn; lia]|]. split; [eapply wr_at_transport; [exact IWR1| exact WM2]|].
  split; [split; [eapply thread_cells_frame; [exact TC1| exact MU2| exact WM2| constructor; [cbn; lia| apply Forall_nil]]| split; [xfer2 T40 MU2 WM2| split; [xfer2 T8 MU2 WM2| xfer2 TU MU2 WM2]]]|].
  split; [xfer2 OBJ MU2 WM2|]. split; [eapply u64arr_transport; [exact ARR| exact MU2| exact WM2| rewrite LEN; cbn; lia]|].
  split; [exact LEN|]. split; [exact FTR|]. split; [exact LTR|].
  split; [xfer2 FR8 MU2 WM2|]. split; [xfer2 FJ1800 MU2 WM2|]. split; [xfer2 FBP MU2 WM2|]. split; [xfer2 FJ8 MU2 WM2|]. split; [xfer2 FJ8B MU2 WM2|].
  replace (usp + -2160) with (usp - 2160) by lia. exact FRA.
Qed.

Lemma rea0_suf_ok : forall (ra s0 s1 s2 s3 s4 s5 s6 t0 t1 t2e a1 a2 a3 a4 a5 a6 a7 s3e s4w t3e t4e t5e t6e bpw : word) (m : mem) (r : Z)
                           (j8 j8b j8c j1800 : list byte) (ws : list word) (len : Z),
  stk asegs m lo (usp - 2160) -> mem_inv asegs m -> 0 < r < 2^64 ->
  rw_cells asegs m (usp + -2160) [CB 8 j8c; C8 (Z_to_bv 64 REA_ASAN_RET)] ->
  rw_cells asegs m (usp + -2144) [CB 8 j8b] ->
  rw_cells asegs m (usp + -2136) [C8 (Z_to_bv 64 (usp + -2120)); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (usp + -2120) ws -> length ws = 30%nat ->
  rw_cells asegs m (usp + -1880) [CB 1800 j1800] -> rw_cells asegs m (usp + -80) [C8 bpw] -> rw_cells asegs m (usp + -72) [CB 8 j8] ->
  rw_cells asegs m (usp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evtA asegs P (rsuf_post ra s0 s1 s2 s3 s4 s5 s6 r 0 [(usp - 2160, usp)] m)
    (MS (mkR (Z_to_bv 64 0x33600) (Z_to_bv 64 (usp - 2160)) gp tp t0 t1 t2e (Z_to_bv 64 usp) (Z_to_bv 64 n)
             (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s3e s4w (Z_to_bv 64 (usp + -2136)) (Z_to_bv 64 (usp + -89)) s7 s8 s9 s10 s11 t3e t4e t5e t6e)
        F (ret_pc (Z_to_bv 64 0x33600)) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros SK MI Hr FRA FJ8B OBJ ARR LEN FJ1800 FBP FJ8 FR8.
  rewrite (ret_pc_even 0x33600) by lia.
  apply rea0_after_ok; [exact Hr|].
  replace (usp - 2160) with (usp + -2160) in * by lia.
  eapply (rea_ret P gp tp t2e _ _ s7 s8 s9 s10 s11 t3e t4e t5e t6e F fc _ lo LOC); [exact SK| lia| lia| exact MI| exact FRA| exact FJ8B| exact OBJ| exact ARR| exact LEN| exact FJ1800| exact FBP| exact FJ8| exact FR8| intros; apply PSTK; lia|].
  intros m6 MI6 SK6 WM6 MU6. apply evtA_done. unfold rsuf_post.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m6. split; [reflexivity|]. split; [intros X; exfalso; exact (X eq_refl)|].
  split; [exact MI6|]. split; [exact SK6|]. split; [exact WM6|]. split; [exact MU6| intros X; exfalso; exact (X eq_refl)].
Qed.

(* [comment removed for export] *)
End RG.
End RC__1.
