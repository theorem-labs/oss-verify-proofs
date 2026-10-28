(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac ImageA Arr Walk Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_small R_m2s R_cache_defs R_prim_defs R_asan_defs R_prim_kit R_glue_defs R_depot_defs R_quar_defs R_qrec_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Lemma firstn_S_nth : forall {X} (l : list X) j x, nth_error l j = Some x -> firstn (S j) l = firstn j l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros j x H; [destruct j; discriminate|].
  destruct j as [|j]; cbn in H; [injection H as ->; reflexivity|]. cbn [firstn app]. f_equal. apply IH. exact H.
Qed.

Section COPY.
Variables (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (CUR NXT t4c t3c : Z) (wc0 wn : list word).
Hypothesis HCN : (CUR + 8192 <= NXT \/ NXT + 8192 <= CUR)%Z.
Hypothesis HCUR : (0 < CUR /\ CUR + 8192 <= 2^47)%Z.
Hypothesis HNXT : (0 < NXT /\ NXT + 8192 <= 2^47)%Z.
Hypothesis Ht : (0 <= t4c /\ 1 <= t3c /\ t4c + t3c <= 1021)%Z.
Hypothesis Hwn : length wn = 1021%nat.

Definition copy_post (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t5' : word) (m' : mem) (wc' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (NXT + 24 + 8 * t3c)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (Z_to_bv 64 (CUR + 24 + 8 * (t4c + t3c))) (Z_to_bv 64 (NXT + 24 + 8 * t3c)) t5' t6)
             F (Z_to_bv 64 0x5b6f8) fc None m' (seg_rom bsegs)
    /\ munch [(CUR + 24, CUR + 8192)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ u64arr bsegs m' (CUR + 24) wc' /\ length wc' = 1021%nat
    /\ firstn (Z.to_nat (t4c + t3c)) wc' = firstn (Z.to_nat t4c) wc0 ++ firstn (Z.to_nat t3c) wn.

Lemma copy_loop : forall (k : nat) (j : Z) (wc : list word) (m : mem) (t5 : word),
  (t3c - j = Z.of_nat (S k))%Z -> (0 <= j)%Z ->
  u64arr bsegs m (CUR + 24) wc -> length wc = 1021%nat ->
  firstn (Z.to_nat (t4c + j)) wc = firstn (Z.to_nat t4c) wc0 ++ firstn (Z.to_nat j) wn ->
  u64arr bsegs m (NXT + 24) wn -> mem_inv bsegs m ->
  evt bsegs (copy_post m)
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (NXT + 24 + 8 * j)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 (CUR + 24 + 8 * (t4c + j))) (Z_to_bv 64 (NXT + 24 + 8 * t3c)) t5 t6)
        F (Z_to_bv 64 0x5b6e4) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros j wc m t5 Hk Hj AC Hlc Hpre AN MI.
  all: destruct (nth_error wn (Z.to_nat j)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
  all: pose proof (munch_refl [(CUR + 24, CUR + 8192)]%Z m) as MU; pose proof (wmono_refl bsegs m) as WM.
  all: pose proof (u64arr_read bsegs m (NXT + 24) wn j w (Z_to_bv 64 (NXT + 24 + 8 * j)) AN Hw ltac:(lia)
                     ltac:(unfold wa; f_equal; lia)) as RD.
  all: zstep; clear RD; zstep.
  all: pose proof (u64arr_store_ok bsegs m (CUR + 24) wc (t4c + j) (Z_to_bv 64 (CUR + 24 + 8 * (t4c + j))) AC ltac:(lia)
                     ltac:(unfold wa; f_equal; lia)) as SO.
  all: pose proof (u64arr_bound bsegs m (CUR + 24) wc AC) as HBA.
  all: zstep.
  all: pose proof (u64arr_write bsegs m (CUR + 24) wc (t4c + j) w AC ltac:(lia)) as AC'; clear AC.
  all: store_done; clear HBA.
  - zstep. zstep. ifF.
    replace (NXT + 24 + 8 * j + 8)%Z with (NXT + 24 + 8 * t3c)%Z by lia.
    replace (CUR + 24 + 8 * (t4c + j) + 8)%Z with (CUR + 24 + 8 * (t4c + t3c))%Z by lia.
    apply evt_done. unfold copy_post. do 3 eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [rewrite upd_length; exact Hlc|].
    replace (Z.to_nat (t4c + t3c)) with (S (Z.to_nat (t4c + j))) by lia.
    rewrite firstn_upd_snoc by lia. rewrite Hpre, <- app_assoc. f_equal.
    replace (Z.to_nat t3c) with (S (Z.to_nat j)) by lia. rewrite (firstn_S_nth wn _ w Hw). reflexivity.
  - zstep. zstep. ifT.
    replace (NXT + 24 + 8 * j + 8)%Z with (NXT + 24 + 8 * (j + 1))%Z by lia.
    replace (CUR + 24 + 8 * (t4c + j) + 8)%Z with (CUR + 24 + 8 * (t4c + (j + 1)))%Z by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_mono; [eapply (IH (j + 1)%Z _ mm); try eassumption; try lia|] end.
    + rewrite upd_length. exact Hlc.
    + replace (Z.to_nat (t4c + (j + 1))) with (S (Z.to_nat (t4c + j))) by lia.
      rewrite firstn_upd_snoc by lia. rewrite Hpre, <- app_assoc. f_equal.
      replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia. rewrite (firstn_S_nth wn _ w Hw). reflexivity.
    + intros ms' (t5' & m' & wc' & E & MU' & WM' & P). exists t5', m', wc'. split; [exact E|].
      split; [eapply munch_trans; eassumption|]. split; [eapply wmono_trans; eassumption| exact P].
Qed.

End COPY.

Definition qmerge_entry : Z := 0x5b674.

Definition merge_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (FROM TO : Z) (gl : list batch) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ((FROM, FROM + 32) :: (TO, TO + 32) :: (bv_unsigned sp - 16, bv_unsigned sp) :: bivs gl)%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ qcache_rep m' FROM (fst (merge_all gl)) /\ qcache_rep m' TO (snd (merge_all gl))
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition merge_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (FROM TO SB lo : Z) (gl : list batch),
  qcache_rep m FROM gl -> qcache_rep m TO [] -> qwf SB gl -> (qbytes gl < 2^56)%Z -> (0 < SB)%Z ->
  (0 < FROM)%Z -> (FROM + 32 <= r24 SB \/ r24 SB + 2^32 <= FROM)%Z -> (TO + 32 <= r24 SB \/ r24 SB + 2^32 <= TO)%Z ->
  (FROM + 32 <= TO \/ TO + 32 <= FROM)%Z -> (bv_unsigned sp <= TO \/ TO + 32 <= lo)%Z ->
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (r24 SB + 2^32 <= lo)%Z -> (FROM + 32 <= lo)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv bsegs m ->
  evt bsegs (merge_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FROM TO gl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FROM) (Z_to_bv 64 TO) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 qmerge_entry) fc None m (seg_rom bsegs)).
