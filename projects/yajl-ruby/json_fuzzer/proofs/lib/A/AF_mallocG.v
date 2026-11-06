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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_kit AF_kit3 AF_unwind AF_unwind_walk2 AF_depot2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanConsts AsanState AsanOps.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

Ltac cstep := stepA; try first [if_true | if_false].
Ltac is_lit t := idtac; lazymatch t with
  | Z.add ?a ?b => is_lit a; is_lit b | Z.sub ?a ?b => is_lit a; is_lit b | Z.mul ?a ?b => is_lit a; is_lit b
  | Z.opp ?a => is_lit a | Z.land ?a ?b => is_lit a; is_lit b | Z.lor ?a ?b => is_lit a; is_lit b
  | Z.shiftl ?a ?b => is_lit a; is_lit b | Z.shiftr ?a ?b => is_lit a; is_lit b | Z.modulo ?a ?b => is_lit a; is_lit b | Z.div ?a ?b => is_lit a; is_lit b
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac is_num t := idtac; lazymatch t with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac evalc e := is_lit e; assert_fails (is_num e); let v := eval vm_compute in e in change e with v.
Ltac litc :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?e] => evalc e
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => is_num e; rewrite (unsigned_lit e) by (clear; lia)
  end.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
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
Definition A_MALLOC_ICPT : Z := 0x54274.     (* [comment removed for export] *)
Definition A_ALLOC_RET : Z := 0x32bd0.       (* [comment removed for export] *)

Section MG.
Variable P : acc -> Prop.
Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo n : Z) (TSD CTX T top bot : Z).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp + -2400.
Hypothesis SPH : usp < 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis Hn : 0 <= n < 2^64.
Hypothesis HTSD : 0x5cfdd0 <= TSD /\ TSD + 8 <= 0x603000.
Hypothesis HCTX : 0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling.     (* [comment removed for export] *)
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.           (* [comment removed for export] *)
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTP : 0x5cfdd0 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000.
Hypothesis HTB : 0 <= bot < top /\ top <= 2^47.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= 2^64 -> P (Z_to_bv 64 a, k).   (* [comment removed for export] *)
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PTHR : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Definition mpre_post (ra s0 s1 s2 s3 s4 s5 : word) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a6 a7 s2w s3w s5w t3 t4 t5 t6 : word) (m1 : mem) (ws tr : list word) (bpw : word) (j1800 j8 : list byte),
    ms = MS (mkR (Z_to_bv 64 A_ALLOC_RET) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n)
                 (Z_to_bv 64 0xaa518) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                 s2w s3w (Z_to_bv 64 (usp + -2128)) s5w s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x32c00) fc None m1 (seg_rom asegs)
    /\ munch [(usp + -2400, usp); (T + 3168, T + 3169)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -2144)
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ u64arr asegs m1 (usp + -2112) ws /\ length ws = 30%nat /\ (1 <= length tr <= 30)%nat /\ firstn (length tr) ws = tr
    /\ rw_cells asegs m1 (T + 3168) [C1 (Z_to_bv 8 0)]
    (* [comment removed for export] *)
    /\ rw_cells asegs m1 (usp + -2144) [C8 (Z_to_bv 64 usp); C8 (Z_to_bv 64 0x543a8)]
    /\ rw_cells asegs m1 (usp + -1872) [CB 1800 j1800]
    /\ rw_cells asegs m1 (usp + -72) [C8 bpw]
    /\ rw_cells asegs m1 (usp + -64) [CB 8 j8]
    /\ rw_cells asegs m1 (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] /\ rw_cells asegs m1 (usp + -16) [C8 s0; C8 ra].

Lemma malloc_pre : forall (ra s0 s1 s2 s3 s4 s5 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
  stk asegs m lo usp -> mem_inv asegs m ->
  rw_cells asegs m 0xae858 [C1 (Z_to_bv 8 1)] ->                                                 (* [comment removed for export] *)
  rw_cells asegs m 0xae87c [C4 (Z_to_bv 64 30)] ->                                                (* [comment removed for export] *)
  rw_cells asegs m 0xa49a0 [C8 (Z_to_bv 64 0x13f6a8)] ->                                         (* [comment removed for export] *)
  rw_cells asegs m 0x13f6ca [C1 (Z_to_bv 8 1)] ->                                                 (* [comment removed for export] *)
  rw_cells asegs m 0xa4990 [C8 (Z_to_bv 64 0x13d620)] -> rw_cells asegs m 0x13d620 [C8 (Z_to_bv 64 4096)] ->   (* [comment removed for export] *)
  uthread_cells m tp TSD CTX T top bot ->
  uanchor asegs m usp ra s0 ->
  evtA asegs P (mpre_post ra s0 s1 s2 s3 s4 s5 m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 A_MALLOC_ICPT) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros SK MI AI GMC GCF CFU GPS PSC TC UA. unfold A_MALLOC_ICPT.
  pose proof LOC as LOC0. pose proof LOC as LOCu. aceil.
  pose proof HT as HT'. aceil. destruct HT' as [HTa HTb].
  pose proof HCTX as HC'. aceil. destruct HC' as [HCa HCb].
  assert (SPR : 0 <= usp < 2^64) by lia.
  assert (MU : munch [(usp + -2400, usp); (T + 3168, T + 3169)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  destruct TC as ((TC1 & TC2 & TC3 & TC4 & TC5) & T40 & T8 & TU).
  assert (PSTK1 : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k)) by (intros; apply PSTK; lia).
  carve_frame 56%nat SK.     (* [comment removed for export] *)
  carve_frame 8%nat SK. rename FR0 into FJ8.     (* [comment removed for export] *)
  carve_frame 8%nat SK. rename FR0 into FBP.     (* [comment removed for export] *)
  carve_frame 1800%nat SK. rename FR0 into FJ1800. (* [comment removed for export] *)
  carve_frame 240%nat SK. rename FR0 into FBUF.  (* [comment removed for export] *)
  carve_frame 16%nat SK. rename FR0 into FOBJ.   (* [comment removed for export] *)
  do 8 zstepA.                        (* [comment removed for export] *)
  do 4 zstepA.                        (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  pose proof (unsigned_lit (usp + -2128) ltac:(lia)) as Hsp.
  callA (try_init_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo); rewrite ?Hsp;
    [exact SK| exact LOC0| lia| lia| exact MI| exact AI| intros; apply PSTK; lia| exact PDAT|].
  rewrite ?Hsp in *. match goal with H : stk _ _ lo _ |- _ => rename H into SK end.
  zstepA; if_cases K0; zify_cond K0; [exfalso; revert K0; rewrite ?unsigned_lit by (clear; lia); clear; lia|]. clear K0.   (* [comment removed for export] *)
  do 5 zstepA.                        (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  leafA (gmcs_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30); [eassumption| lia| exact GMC| exact PDAT|].
  zstepA. cstep.                      (* [comment removed for export] *)
  zstepA. leafA (getpc_walk P); [eassumption|].
  zstepA. zstepA.                     (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  zstepA. leafA (gmcs_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 30); [eassumption| lia| exact GMC| exact PDAT|].
  do 5 zstepA.                        (* [comment removed for export] *)
  litc. replace (Z.land 18446744073709551615 usp) with usp
    by (change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; symmetry; apply Z.mod_small; lia).
  zstepA.                             (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  do 6 zstepA.                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (FOBJ2 : rw_cells asegs mx (usp + -2128) ([C8 (Z_to_bv 64 (usp + -2112))] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]))
      by (eapply rw_cells_reshape; [| | exact FOBJ]; [cbn; tauto| reflexivity]) end.
  clear FOBJ. apply rwc_split in FOBJ2. destruct FOBJ2 as [FOBJ CSZ]. cbn [cells_size csize Nat.add] in CSZ.
  replace (usp + -2128 + Z.of_nat 8) with (usp + -2128 + 8) in CSZ by lia.
  change [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] with ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]) in CSZ.
  apply rwc_split in CSZ. destruct CSZ as [CSZ TAG]. cbn [cells_size csize Nat.add] in TAG.
  replace (usp + -2128 + 8 + Z.of_nat 4) with (usp + -2128 + 12) in TAG by lia.
  destruct (u64arr_of_cb asegs _ _ _ 30 FBUF) as (ws0 & LEN0 & ARR0). clear FBUF.
  change [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] with ([C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR.
  apply rwc_split in FR. destruct FR as [FR CL]. cbn [cells_size csize Nat.add] in CL.
  replace (usp + -56 + Z.of_nat 40) with (usp + -16) in CL by lia.
  zstepA.                             (* [comment removed for export] *)
  callA (unwind_impl_walk2 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo _ _ TSD CTX T top bot _ _ ws0 s0 ra);
    rewrite ?Hsp;
    [exact SK| exact LOC0| lia| lia| lia| lia| lia| lia| eassumption| exact AI| exact GPS| exact PSC
    | exact (conj (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5)))) (conj T40 (conj T8 TU)))
    | lia| lia| lia| exact (proj2 HCTX)| exact (proj1 HT)| exact (proj2 HT)| exact HTC| lia
    | exact CSZ
    | replace (usp + -2128 + 16) with (usp + -2112) by lia; exact ARR0| exact LEN0
    | replace (usp + -2128 + 2056) with (usp + -72) by lia; exact FBP
    | exact CL
    | eapply uanchor_frame; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia
    | exact PSTK| exact PDAT| exact PCTX| exact PTHR|].
  rewrite ?Hsp in *. match goal with H : stk _ _ lo _ |- _ => rename H into SK end.
  rename PC0 into UARR. rename PC1 into ULEN. rename PC2 into UFST. rename PC3 into UBND. rename PC4 into UHD. rename PC6 into UBP. rename POST into TUk.
  lazymatch type of UFST with firstn (length ?a) ?bb = _ => rename a into tr; rename bb into ws end.
  do 3 zstepA.                        (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  carve_frame 16%nat SK. rename FR0 into FAM.
  do 3 zstepA.                        (* [comment removed for export] *)
  do 7 zstepA.                        (* [comment removed for export] *)
  zstepA.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (rwc_join_at asegs mx _ _ _ _ PC5 TAG ltac:(cbn; lia)) as ST8; cbn [app] in ST8;
    apply (rw_cells_c8_join asegs mx _ (Z.of_nat (length tr)) 0 []) in ST8; [| clear -CEILB UBND; lia| clear; lia];
    pose proof (rwc_join_at asegs mx _ _ _ _ FOBJ ST8 ltac:(cbn; lia)) as OBJ; cbn [app] in OBJ; clear ST8 PC5 FOBJ end.
  replace (Z.of_nat (length tr) + 2 ^ 32 * 0) with (Z.of_nat (length tr)) in OBJ by (clear; lia).
  replace (usp + -2128 + 16) with (usp + -2112) in UARR by lia.
  replace (usp + -2128 + 2056) with (usp + -72) in UBP by lia.
  apply evtA_done. unfold mpre_post, A_ALLOC_RET. litc.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end.
  all: try first [ eassumption | exact ULEN | exact UFST | clear -CEILB UBND; lia ].
  Unshelve. all: try exact (Z_to_bv 64 0).
Qed.

(* [comment removed for export] *)
Definition msuf_post (ra s0 s1 s2 s3 s4 s5 : word) (r : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(usp + -2400, usp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
    /\ (r = 0 -> rw_cells asegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 12)])
    /\ (r <> 0 -> forall e, rw_cells asegs m (bv_unsigned tp + -164) [C4 e] -> rw_cells asegs m' (bv_unsigned tp + -164) [C4 e]).

Lemma malloc_suf : forall (ra s0 s1 s2 s3 s4 s5 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2w s3w s5w t3 t4 t5 t6 errw bpw : word) (m : mem)
                          (r : Z) (ws : list word) (len : Z) (j1800 j8 : list byte),
  stk asegs m lo (usp + -2144) -> mem_inv asegs m -> 0 <= r < 2^64 ->
  rw_cells asegs m (bv_unsigned tp + -164) [C4 errw] ->
  rw_cells asegs m (usp + -2144) [C8 (Z_to_bv 64 usp); C8 (Z_to_bv 64 0x543a8)] ->
  rw_cells asegs m (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C8 (Z_to_bv 64 len)] ->
  u64arr asegs m (usp + -2112) ws -> length ws = 30%nat ->
  rw_cells asegs m (usp + -1872) [CB 1800 j1800] -> rw_cells asegs m (usp + -72) [C8 bpw] -> rw_cells asegs m (usp + -64) [CB 8 j8] ->
  rw_cells asegs m (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] -> rw_cells asegs m (usp + -16) [C8 s0; C8 ra] ->
  evtA asegs P (msuf_post ra s0 s1 s2 s3 s4 s5 r m)
    (MS (mkR (Z_to_bv 64 A_ALLOC_RET) (Z_to_bv 64 (usp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
             s2w s3w (Z_to_bv 64 (usp + -2128)) s5w s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 A_ALLOC_RET) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until j8. intros SK MI HR ERR FAM OBJ ARR LEN FJ1800 FBP FJ8 FR CL. unfold A_ALLOC_RET.
  pose proof LOC as LOC0. pose proof LOC as LOCu. aceil.
  pose proof (bv_unsigned_in_range 64 tp) as TPR. unfold bv_modulus in TPR. cbn in TPR.
  assert (SPR : 0 <= usp < 2^64) by lia.
  assert (MU : munch [(usp + -2400, usp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  assert (PSTK1 : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k)) by (intros; apply PSTK; lia).
  pose proof (cb_of_u64arr asegs _ _ _ ARR) as TRC. rewrite LEN in TRC. cbn [Nat.mul Nat.add] in TRC. clear ARR.
  assert (TAIL : forall (t0' t1' t2' a1' a6' a7' : word) mm,
    munch [(usp + -2400, usp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m mm -> wmono asegs m mm -> mem_inv asegs mm -> stk asegs mm lo (usp + -2144) ->
    rw_cells asegs mm (usp + -2144) [C8 (Z_to_bv 64 usp); C8 (Z_to_bv 64 0x543a8)] ->
    rw_cells asegs mm (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C8 (Z_to_bv 64 len)] ->
    rw_cells asegs mm (usp + -2112) [CB 240 (u64s ws)] ->
    rw_cells asegs mm (usp + -1872) [CB 1800 j1800] -> rw_cells asegs mm (usp + -72) [C8 bpw] -> rw_cells asegs mm (usp + -64) [CB 8 j8] ->
    rw_cells asegs mm (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] -> rw_cells asegs mm (usp + -16) [C8 s0; C8 ra] ->
    (r = 0 -> rw_cells asegs mm (bv_unsigned tp + -164) [C4 (Z_to_bv 64 12)]) ->
    (r <> 0 -> forall e, rw_cells asegs m (bv_unsigned tp + -164) [C4 e] -> rw_cells asegs mm (bv_unsigned tp + -164) [C4 e]) ->
    evtA asegs P (msuf_post ra s0 s1 s2 s3 s4 s5 r m)
      (MS (mkR (Z_to_bv 64 0x32bd0) (Z_to_bv 64 (usp + -2144)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 n) (Z_to_bv 64 r) a1' a2 a3 a4 a5 a6' a7'
               s2w s3w (Z_to_bv 64 (usp + -2128)) s5w s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x32bd4) fc None mm (seg_rom asegs))).
  { clear MU WM MI SK FAM OBJ TRC FJ1800 FBP FJ8 FR CL ERR.
    intros t0' t1' t2' a1' a6' a7' mm MU WM MI SK FAM OBJ TRC FJ1800 FBP FJ8 FR CL E0 E1.
    do 3 zstepA.                        (* [comment removed for export] *)
    release_frame FAM SK (usp + -2128).
    cstep.                              (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    do 7 zstepA.                        (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    release_frame OBJ SK (usp + -2112). release_frame TRC SK (usp + -1872). release_frame FJ1800 SK (usp + -72).
    release_frame FBP SK (usp + -64). release_frame FJ8 SK (usp + -56). release_frame FR SK (usp + -16). release_frame CL SK usp.
    cstep.                              (* [comment removed for export] *)
    apply evtA_done. unfold msuf_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [litc; reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    all: first [ match goal with H : stk _ _ lo ?u |- _ => replace usp with u by lia; exact H end | idtac ]. }
  zstepA; if_cases KZ; zify_cond KZ.
  - (* [comment removed for export] *)
    assert (R0 : r = 0) by (revert KZ; rewrite ?unsigned_lit by lia; clear -CEILB HR; first [lia | intros KZ; rewrite Z_to_bv_small in KZ by (change (bv_modulus 64) with (2^64); lia); lia]).
    subst r.
    zstepA.                             (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    carve_frame 16%nat SK.
    zstepA. zstepA.                     (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    zstepA. zstepA. zstepA.             (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    zstepA. zstepA.                     (* [comment removed for export] *)
    release_frame FR0 SK (usp + -2144).
    zstepA.                             (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    (* [comment removed for export] *)
    do 3 zstepA.                        (* [comment removed for export] *)
    release_frame FAM SK (usp + -2128).
    cstep.                              (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    do 7 zstepA.                        (* [comment removed for export] *)
    zstepA.                             (* [comment removed for export] *)
    release_frame OBJ SK (usp + -2112). release_frame TRC SK (usp + -1872). release_frame FJ1800 SK (usp + -72).
    release_frame FBP SK (usp + -64). release_frame FJ8 SK (usp + -56). release_frame FR SK (usp + -16). release_frame CL SK usp.
    cstep.                              (* [comment removed for export] *)
    apply evtA_done. unfold msuf_post. repeat (lazymatch goal with |- ex _ => eexists end). split; [litc; reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    all: try match goal with H : stk _ _ lo ?u |- _ => replace usp with u by lia; exact H end.
    + intros _. lazymatch goal with |- rw_cells _ ?mx ?a _ => match goal with H : rw_cells asegs mx _ [C4 (Z_to_bv 64 12)] |- _ => first [exact H | replace a with (bv_unsigned tp + -164) by lia; exact H] end end.
    + intros NE. exfalso. exact (NE eq_refl).
  - (* [comment removed for export] *)
    assert (RN : r <> 0) by (revert KZ; rewrite ?unsigned_lit by lia; intros KZ; first [lia | rewrite Z_to_bv_small in KZ by (change (bv_modulus 64) with (2^64); lia); lia]).
    eapply TAIL; try eassumption.
    + intros E0. exfalso. exact (RN E0).
    + intros _ e He. exact He.
Qed.
End MG.
End RC__1.
