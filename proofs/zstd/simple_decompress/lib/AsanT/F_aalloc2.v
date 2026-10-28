(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AModelFacts F_memset F_apoison F_aalloc_s.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition hdr_b1_mid (b1 : Z) : Z := Z.lor (Z.land (Z.lor (Z.land b1 18446744073709551612) 1) 143) 16.

Notation allocBC_W L sp UB PG pgw n :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_post (L : alayout) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t AB UB PG pgw lo b0 b1 : Z) (pj : byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x34054) fc None m' (seg_rom bsegs)
    /\ munch (allocBC_W L sp UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 (hdr_b1_mid b1)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

(* [comment removed for export] *)
Lemma partial_spec : forall RNG (n UB PG pgw : Z) (pj : byte) ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  mem_inv bsegs m ->
  1 <= n <= 448 -> PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  ablk UB (UB + n) -> UB + n <= ATOP -> UB mod 8 = 0 ->          (* [comment removed for export] *)
  rw_cells bsegs m 0xc72f8 [C8 (Z_to_bv 64 0x161828); C8 (Z_to_bv 64 0xcd4f8); C8 (Z_to_bv 64 0xcfcf8);
                             C8 (Z_to_bv 64 0xd09e8); C8 (Z_to_bv 64 0xd09f0); C8 (Z_to_bv 64 0xd09e0)] ->
  rw_cells bsegs m 0xcfcf8 [C8 (Z_to_bv 64 0x7fff8000)] ->
  rw_cells bsegs m 0xd09e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xcf55c [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xcd54d [C1 (Z_to_bv 8 1)] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  rng_aimg RNG -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF bsegs RNG (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' a6' a7' s6' m',
      ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 UB) s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34054) fc None m' (seg_rom bsegs)
      /\ munch [(PG, PG + pgw)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 UB) s5 (Z_to_bv 64 (n - n mod 8)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33fc0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI N HPG HPW UBLO UBHI UB8 GOT SHB LAY CANP PP SHP RIMG RPG.
  pose proof (munch_refl [(PG, PG + pgw)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold ablk, AIMG_HI, KLS in UBLO. atop_facts.                (* [comment removed for export] *)
  assert (SHR : 0x7fff8000 <= shad UB /\ 0 <= shlen (n - n mod 8) <= 56 /\ PG + 1 <= 0x10007fff8000).
  { unfold shad, shlen, ASHOFF in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. Z.div_mod_to_equations. lia. }
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  { apply evtF_done. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. intros NE. exfalso. lia. }
  specialize (SHP ltac:(lia)). specialize (RPG ltac:(lia)).
  assert (PW1 : pgw = 1) by (rewrite HPW; destruct (Z.eqb_spec (n mod 8) 0); [lia|reflexivity]). clear HPW. subst pgw.
  step. callp can_poison_spec; [exact CANP|]. step. if_lit.      (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  change (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879.
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  2: step; step; step; step; step; step; zstep.                  (* [comment removed for export] *)
  2: step; if_cases K2; zify_cond K2; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; step; step; zstep; zstep.                             (* [comment removed for export] *)
  2: step; if_cases K3; zify_cond K3; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: step; step; lstep; zstep; zstep.                          (* [comment removed for export] *)
  all: setreg 10 (Z_to_bv 64 PG) ltac:(rewrite HPG; unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; f_equal; Z.div_mod_to_equations; lia).
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: rewrite (land_ones_r n) by lia; change 7 with (2^3 - 1) at 1; rewrite (zb_land_mask n 3) by lia; change (2^3) with 8.
  all: sstep.                                                    (* [comment removed for export] *)
  all: apply evtF_done; do 11 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|].
  all: intros _; assumption.
Qed.



Lemma allocBC_spec : forall (L : alayout) RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (pj : byte) (sj : list byte)
    (tb : list word) (tr : list Z) (fr0 : list byte) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= 448 ->
  (* [comment removed for export] *)
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  (* [comment removed for export] *)
  (t + 4096 <= AB \/ AB + 65536 <= t) -> sclr t 4096 ->
  (al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) -> sclr (al_ctx L) 65536 ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> sclr (al_nodes L) 1048576 ->
  (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) -> sclr (al_store L) 8388608 ->       (* [comment removed for export] *)
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sj] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  (* [comment removed for export] *)
  poison_cells m -> rw_cells bsegs m 0xcd54d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->       (* [comment removed for export] *)
  (* [comment removed for export] *)
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  evtF bsegs RNG (allocBC_post L sp gp tp F fc n S t AB UB PG pgw lo b0 b1 pj m)
    (MS (mkR (Z_to_bv 64 0x33da8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33da8) fc None m (seg_rom bsegs)).
Proof.
  intros until s11v.
  intros ST CEIL LO MI TP N HUB ABLO UBHI AB16 NSZ HPG HPW DJT SHT DJC SHC DJN SHN DJS SHS SB1 SB2 SB3 SB4 FR HDR B1 SHA SHU SHP PC PP CT8 TT0 CX0 CX1 T0 T1
         SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1 RIMG RSTK RS RNO RST RCTX RT RHD RSA RSU RSP. band_lin.   (* [comment removed for export] *)
  assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (UB16 : UB mod 16 = 0).
  { rewrite HUB. pose proof (rz_size_small_cases n N). clear -AB16 H. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  pose proof (munch_refl (allocBC_W L sp UB PG pgw n) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS.
  snapshot [(UB - 16, UB)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (UB - 16, UB);
            (shad UB, shad UB + shlen (n - n mod 8));
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  box SHP.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }     (* [comment removed for export] *)
  zstep. setreg 20 (Z_to_bv 64 UB) ltac:(rewrite HUB; reflexivity).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. rewrite HUB, RZE.
       rewrite (rz_log_small n N). clear -AB16 N.
       destruct (n <=? 48); [|destruct (n <=? 96)]; cbn; Z.div_mod_to_equations; lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. lia. }              (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }             (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros a Ha. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. lia. }
  clear MUh WMh. box HDR.
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  box SHA. box SHU.          (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 64, bv_unsigned sp + -128); (UB - 16, UB); (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; lia).
  carry SHA MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)). carry SHU MUd WMd ltac:(with_band SHN ltac:(with_band SHS lia)).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. step. step. zstep. zstep.                                (* [comment removed for export] *)
  setreg 10 (Z_to_bv 64 (shad AB)) ltac:(unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  step. zstep. zstep.                                            (* [comment removed for export] *)
  rewrite (land_align8_48 n) by lia.
  step. if_cases K4; zify_cond K4.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xc72f8 _ => exact PC1
         | |- rw_cells _ _ 0xcfcf8 _ => exact PC4
         | |- rw_cells _ _ 0xd09e0 _ => exact PC5
         | |- rw_cells _ _ 0xcf55c _ => exact PC6
         | |- rw_cells _ _ 0xcd54d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_post. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    (* [comment removed for export] *)
    rewrite K4. rewrite K4 in SHU. pose proof SHU as W0. destruct W0 as [[[WF X1] X2] X3]. cbn in WF. destruct sj; [exact SHU| cbn in WF; discriminate].
  - (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UB (n - n mod 8) 0 lo sj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => eassumption
         | |- mem_inv _ _ => assumption
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ (shad _) _ => exact SHU
         end.
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- rng _ _ _ => solve_rng
         | |- ablk _ _ => unfold ablk; right; atop_facts; lia
         | |- _ => atop_facts; first [lia | Z.div_mod_to_equations; lia]
         end.
    (* [comment removed for export] *)
    unbox SHP.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHP' : n mod 8 <> 0 -> rw_cells bsegs mm PG [C1 pj]) end.
    { intros NE. specialize (SHP NE). box SHP. carry SHP MUq WMq ltac:(with_band SHN ltac:(with_band SHS lia)). exact SHP. }
    clear SHP MUq WMq.
    call (partial_spec RNG n UB PG pgw pj).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption   (* [comment removed for export] *)
         | |- mem_inv _ _ => assumption
         | |- PG = _ => exact HPG
         | |- _ = (if _ then _ else _) => exact HPW
         | |- rw_cells _ _ 0xc72f8 _ => exact PC1
         | |- rw_cells _ _ 0xcfcf8 _ => exact PC4
         | |- rw_cells _ _ 0xd09e0 _ => exact PC5
         | |- rw_cells _ _ 0xcf55c _ => exact PC6
         | |- rw_cells _ _ 0xcd54d _ => exact PP
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> rng _ _ _ => exact RSP
         | |- ~ _ -> _ => exact SHP'
         | |- ablk _ _ => unfold ablk; right; lia
         | |- _ => lia
         end.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) end.
    { eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |].
      repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha DJN DJS SHN SHS SB1 SB2 SB3 SB4 HPG PW01 N0 N1 R0 R1 CEIL LO SPR S47 SPS HUB ABLO UBHI NSZ NS RZR RSR NSR; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia) | pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; with_band SHN ltac:(with_band SHS lia)]|]).   (* [comment removed for export] *)
      apply Forall_nil. }
    apply evtF_done. unfold allocBC_post. do 19 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact IDR|].
    split; [exact HDR|]. split; [| split; [assumption| exact DEPF]].
    assumption.
Qed.
End WithDepot.
End CANSEC1.
