(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF StepF ExecF ITreeA.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes ADepot_iface APoisonR_iface ARep ARepKit ARepFrame.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AModelFacts APrimFacts ASecFacts F_apoison F_rsrvshadow F_alarge F_aalloc F_aalloc2g F_aalloc_s F_aalloc3g F_amalloc_iseg F_amalloc_icpt F_aalloc2s F_aalloc3s.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. Local Ltac2 Set LiaHints.tbl := fun () => "0020=37386272180.657630483300.600000900BS1H2H12H0S1H2H12H0".
destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148232192 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=29376364801.838731552529.800000<00ES1H2H12A82H0S1H2H12A8".
destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
(* [comment removed for export] *)
#[using="Type"] Local Lemma premap_cells_frame_b : forall m m' W, premap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI, AIMG_LO in HW.
  assert (D : forall A k, 0 <= k -> 0x10000 <= A -> A + k <= 0x5f6000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA0 HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.
#[using="Type"] Lemma skipn_repeat {A} (x : A) : forall k n, skipn k (repeat x n) = repeat x (n - k).
Proof. induction k as [|k IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
#[using="Type"] Lemma firstn_repeat' {A} (x : A) : forall k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0020=32563571660.67733768704.7 000003006S1HS1H".
induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. f_equal. apply IH. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma zeros16_hdr : forall m A, fill_at m A 16 0 ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fill_cut : forall m A len k v, fill_at m A len v -> 0 <= k <= len ->
  fill_at m A k v /\ fill_at m (A + k) (len - k) v.
Proof. intros m A len k v H HK. Local Ltac2 Set LiaHints.tbl := fun () => "0030=26934866495.847385330897.851794595714.8000001005009SS2HKS2HK".
replace len with (k + (len - k)) in H by lia. apply fill_split in H; [exact H| lia| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section WithDepot.
Variable DI : ADepotIface.
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation mallocS_W L sp t a ms :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (t + 2800, t + 3168); (a + 4096, a + ms); (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition malloc_postS (L : alayout) (RNG : footprint) (sp : word) (n t a ms nsec lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) (id : Z) (sj' : list word) : Prop :=
  let AB := a + 4096 in let UB := a + 6144 in
     fp_le RNG RNG'
  /\ munch (mallocS_W L sp t a ms) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
  /\ stk bsegs m' lo (bv_unsigned sp)
  /\ 0 < id < 2^31
  /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)]
  /\ junk_at m' (a + 32) (4096 - 32)
  /\ rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]
  /\ junk_at m' (AB + 16) (2048 - 32)
  /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
  /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]
  /\ junk_at m' (UB + n) (ms - 6144 - n)
  /\ fill_at m' (shad a) 768 0xfa
  /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)]
  /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
  /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

#[using="PR"] Lemma malloc_tail_sec : forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    (ra sp gp tp spA : word) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i : word)
    (F : bvmap 5 word) fc (m : amem)
    (n t a ms nsec SB lo sz : Z) (fr0 junk2 : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  bv_unsigned spA = bv_unsigned sp - 2144 ->
  stk bsegs m lo (bv_unsigned sp - 2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= ctx \/ ctx + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells bsegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                      CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))] ->
  rw_cells bsegs m AB [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))] ->
  fill_at m (shad a) 512 0xfa -> fill_at m (shad a + 512) (size / 8) 0 -> fill_at m (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0x9e88d [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 SB)] -> rw_cells bsegs m 0x9da18 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0x9e864 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x99c68 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5d3fe0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x132b00 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  (exists sj, u64arr bsegs m (t + 2800) sj /\ length sj = 46%nat) ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  (* [comment removed for export] *)
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp - 2272)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
      C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x31200)] ->
  rw_cells bsegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x523dc)] ->
  rw_cells bsegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = AMALLOC_PC :: tr ->
  In (AMALLOC_PC :: tr) (al_U L) -> bv_unsigned sp < 2^47 ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ADEPOT DI L m ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG' m' id sj' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     malloc_postS L RNG sp n t a ms nsec lo m RNG' m' id sj' ->
     implS bsegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 UB) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0 t1 t2
             (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
             (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x314d0) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros HspA ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS
         HDRP ZB SHF1 SHZ SHF2 PC PMC RELRO PP I32 I64 FLG HK MCS CF34 TI TK T88 TSD CT CX8 TT0 [sj [STATS LSJ]]
         CX0 CX1 CXS T0 T1 TS CT2 DTN DTS DCN DCS N0 N1 R0 R1 FRa FR16 SS SZ SZB TB LTB TRF TRU S47 FRS DEP
         RIMG RSTK RCTX RT RNO RST RA RSA NI SI KONT. band_lin.   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB). rewrite <- HMS in MSE, MSR, MSM, MSB.
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, AMALLOC_PC in *.
  word_range sp SPR.
  (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8
               /\ needed_size n / 8 = 512 + granules n
               /\ granules n = shlen (n - n mod 8) + (if n mod 8 =? 0 then 0 else 1)
               /\ shlen n = shlen (n - n mod 8)).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. rewrite NSE, RSE.
    Local Ltac2 Set LiaHints.tbl := fun () => "02J0?1090018621.4   1091167832.32  11480693016.1  12242801608.34 1273237474.293 13157035194.20913367077700.34 1370718544.2   15043033658.25916258539767.23 16296064967.46 16947070035.26517941913494.30517986879152.29318435116950.30518477764938.29319469227460.2  19617313304.64 19821252179.34 19821252179.35 19969812475.20220114434585.24 20257126714.4  21165803625.23 21465784861.2  2146705260.34  2260012882.3   22610759855.34 23549655718.24 23779009444.55 24045481643.20724505486483.26525118234422.34 25215756967.35 26326327891.26527728603717.24 27983035420.8  2867937305.35  29206038893.32 29252585207.35 29600199198.6  29713811132.34 31779590777.9  31919345619.26533150580842.34 33323294083.34 33669827455.46 33707107672.23 33794652781.34 34326450181.2  35084517586.34 35155443732.34 35750959173.15 35763923656.34 36326415890.34 36329091450.4  36433628150.5  36581879715.10 37019857342.6  37386977061.55 37521781242.34 37592147547.2933844491588.34  3846277091.198 38470913477.4  38985769492.34 39045777613.34 39045777613.35 39133011934.2  40864623135.4  41474083634.2  42268710382.46 42493948420.20143070470895.34 43358680699.4  44774141435.26645680264602.34 46382461690.54 47455394259.26548222090691.6  48376404837.46 49230004550.4  49235237366.34 49512687514.34 49560432898.5  49742601483.34 50185376437.3  50373358441.32 50487448385.16 50732416736.4  52078783187.26552217312979.26552569147371.24 52569147371.26552569147371.26852569147371.27352569147371.29152584916207.34 52899752024.32 53789669474.4  54322716781.23 54963388153.2  54963601145.2  54965745474.2  54969794426.55 55945525878.34 56183017113.26556185111960.20756190251474.9  56956174629.54 57022093363.2095747013779.265 57568010350.35 57993619733.54 58608663729.2  58757823478.34 58949359537.34 58949359537.35 59308587280.16 59678942912.15 59755918283.32 60234007675.34 60640299157.46 61143463741.34 61331928280.34 61514423692.24 62412609899.24 62883037913.6  63978123772.29364151693579.2656463275323.15  64929919611.25965449328565.20865573642421.20365621023708.26566106723726.4  663571926.34   663571926.35   66634818178.3  66994183538.34 67052580601.32 67332110327.32 67342682210.4  6737307294.207 67469470029.48 67625901322.2096775148421.34  67861152336.4  68690665677.35 7260281738.292 7898010261.32  8203316926.6   8806422860.16  9729791282.291 00000100D00E00K01001=01>01C01P01\01b02O02a03803J03_03d03e04I04h05505B05C05D05I05e05j06F06^06o07?07l08C08F09309409A09N09b09j0:90:J0:`0;M0;\0;]0<00<10<B0<G0<V0<\0<g0<h0<n0=10=50=B0=Q0=U0=V0=h0=i0>60>70>=0>V0>f0>k0?80?<0?c0@00@?0@E0@R0@a0@b0AO0A^0A_0A`0B10B@0BD0BJ0BK0B^0Bd0Be0CR0D?0DW0Ee0H50I>0JJ0JY0Jl0K10KB0KF0KJ0KO0KT0L80LJ0L\0Lk0Lo0M<0Mi0ND0NI0NN0N_0O;0OR0OS0OY0P40PO0Pc0Q20QK0QN0Qf0R70RI0RZ0R^0Rk0S^0Sk0T<0T=0TY0U00U50UN0Ua0V<0VA0VN0WC0WP0W_0W`0X;0XM0Xa0Y00YB0YTSS3MSB4ASDa4ASDb3MS8SS4ALO1S1N3LSJ3LTB3MSB4ALO13AZ05ABNDd4LSJd1HS3LSJ3LTB3AZ0SS3AALS3LSJ3LTB3AZ0S3MSB4ALO11YS4SHB1S4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS3LSJ3LTB3AZ04LSJdS4CEIL3LSJ3LTB3AZ04LSJdS3LSJ3LTB3AZ04LSJdS2LO3LSJ3LTB3AZ04LSJdS3SG5FS3SG23SG54SHB15TBNDa5TBNDb4SGX14SGX2S3SG23SG54SHB15TBNDa5TBNDb4SGX1S3LSJ3LTB3AZ0S4CEIL2LO3AHISSS3SG5S3SG23SG54ASDa4ASDb3MS64SGX2S3SG5S3MSB3SG23SG54ASDa4ASDb4SGX2S4CEIL2LO3AHI3MSB4ALO11YS3AHI3RSR3NSE3MSRS2LO3LSJ3LTB3AZ0S4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS3RSR3NSE3MSR4ASDa4ASDbS1NS4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HSS3RSR3NSE3MSRS4CEIL2LO3AHIS4CEIL2LO4SHB23MS81HS1N4ALO1S1N3RSR3NSE3MSRS4CEIL2LO3AHI3MSBS3RSE3NSE3MSR3SG94SHB2S4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS3MSB4ALO11Y2Y0SS3MSB4ASDa4ASDb3MS8SS4CEIL2LO3AHI3MSBS3MSBS3MSB4ASDa4ASDbS4ALO1S4CEIL2LO1HSS4ALO1S1NS2E8S3MSE3MSM3SGNS1N3RSR3NSE3MSRS2LOSS3LSJ3LTB3AZ04LSJdSS3LSJ3LTB3AZ0SS4ALO1S4CEIL2LO3SG54SGX14SGX21HS4CEIL2LO4SGX11HS3SG5S3CX11H2N12R1S2T0S4SHB14SHB25NBNDa5NBNDb3MS85SBNDa5SBNDbS3LSJ3LTB3AZ0S3MSB4ALO11Y2Y0S2T11HS3LSJ3LTB3AZ0S3MSB4ASDa4ASDbSS4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS1N3RSR3NSE3MSRSSS4CEIL2LO3AHI3MSBS3MSB4ASDa4ASDbS2E8S4ALO1SS4ASDa4ASDb3MS83MS6S4ALO1FS4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS4CEIL2LO3AHI3MSB4ALO11YS4HspA4CEIL2LO1N3LSJ2N12R13LTB2NB3RSE3RSR3NSE3MSB3SG93SGG3SGS3AZ05ABNDd4SHB21HS4CEIL2LO1N3LSJ2T02T12N12R13LTB2NI2SI2NB3RSE3RSR3NSE3MSE3MSB3SG93SGG3SGS3AZ05ABNDa5ABNDd4SHB14SHB25TBNDa5TBNDb3MS61Y2Y02Y11H3CX03CX15CBNDa5CBNDbS4CEIL2LO1N3LSJ2N12R13LTB2NB3RSE3RSR3NSE3MSB3SG93SGG3SGS3AZ05ABNDd4SHB21HS4CEIL2LO1N3LSJ2T13LTB2NB3RSE3RSR3NSE3MSR3MSB3SG93SGG3SGS3AZ05ABNDd4LSJd3MS6S3MSB4ALO11Y2Y0S3MSB4ASDa4ASDb3MS8S3AALS4CEIL2LO3AHI3MSBS2SIS2NIS3CX0S3CX0S3SG23SG54SHB15TBNDa5TBNDb4SGX14SGX2S4HspA3LSJ3LTB3AZ0S4HspA3LSJ3LTB3AZ0S3RSR3NSE3MSR1YS2LOS3LSJ3LTB3AZ0S4CEIL2LO1N3LSJ3LTB2NI2SI3MSB4ALO13AZ04SHB11HS3RSR3NSE3MSR3MSB4ALO11Y2Y0S3S47S3AALS4CEIL2LO3AHI3MSBS3SG23SG54ASDa4ASDb3MS64SGX2S3SG23SG54ASDa4ASDb3MS6SS4ALO1S4SHB14SHB25TBNDa5TBNDb3MS8S3RSR3NSE3MSR3MSB4ALO11Y2Y0S4CEIL2LO4SHB23MS81HS3MSB4ASDa4ASDbS4CEIL2LO3SG54SGX14SGX21HS1NS3RSR3NSE3MSR3MSB4ALO11YS3RSR3NSE3MSR3MSBS3LSJ3LTB3AZ04LSJdS3LSJ3LTB3AZ03MS6S2T0S3LSJ3LTB3AZ0S4HspA1N3LSJ3LTB2NB3RSE3RSR3NSE3MSB3SG93SGG3SGS3AZ0S3LSJ3LTB3AZ0S3LSJ3LTB3MSB3AZ0SS3MSB3SG23SG54ASDa4ASDb4SGX2S3MSB3SG23SG54ASDa4ASDbS3SG5S4CEIL2LO3AHI3RSR3NSE3MSRS4ASDa4ASDb3MS83MS6S4SHB14SHB25TBNDa5TBNDb3MS8S3AALS3LSJ3LTB3AZ0S4CEIL2LO2N12R12Hx1H2T02NI2SI3MSB4ALO11Y2Y02Y12Y23MS6S3LSJ3LTB3AZ0S3MSB4ALO11Y2Y0SS3RSR3NSE3MSR3MSB4ASDa4ASDbS3LSJ3LTB3AZ04LSJdS4CEIL2LO4SHB23MS81HS1N3RSR3NSE3MSRS1N3RSR3NSE3MSR2HqS3LSJ3LTB3AZ04LSJd".
repeat split; try (clear -AAL N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    all: destruct (Z.eqb_spec (n mod 8) 0) as [E8|E8]; clear -AAL N E8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SG as (SG1 & SG2 & SG5 & SG6 & SG8 & SG9 & SGN & SGG & SGS).
  pose proof (ablk_lin _ _ ALO) as (ALO1 & AZ0 & _ & _). unfold AIMG_HI in ALO1, NI, SI.   (* [comment removed for export] *)
  destruct (ablk_int _ _ ALO) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd).   (* [comment removed for export] *)
  destruct (ablk_shad_int _ _ ALO ltac:(clear -AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(clear -MSB; lia)) as (kS & ASD & ASDa & ASDb & SHB1 & SHB2).   (* [comment removed for export] *)
  destruct (sclr_int _ _ TS ltac:(clear -T0; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb). destruct (sclr_int _ _ CXS ltac:(clear -CX0; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).   (* [comment removed for export] *)
  destruct (sclr_int _ _ N0 ltac:(clear -NI; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb). destruct (sclr_int _ _ R0 ltac:(clear -SI; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  assert (MS8 : 9216 <= ms / 8 /\ 6144 + n <= ms) by (clear -MSB MSR NSE RSR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia). destruct MS8 as [MS8 MS6].
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2. box DJSB.
  (* [comment removed for export] *)
  pose proof HDRP as HP0. rw_split HP0 4%nat HDR4 PGJ.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)])) with (a + 32) in PGJ by (cbn; lia).
  assert (ZBF : fill_at m (a + 4096) (ms - 4096) 0) by exact ZB. clear ZB.
  destruct (fill_cut m (a + 4096) (ms - 4096) 16 0 ZBF ltac:(clear -MSR NSE RSR N; lia)) as [ZAB Z1].
  destruct (fill_cut m (a + 4096 + 16) (ms - 4096 - 16) 2016 0 Z1 ltac:(clear -MSR NSE RSR N; lia)) as [ZJ1 Z2]. clear Z1.
  replace (a + 4096 + 16 + 2016) with (a + 6128) in Z2 by lia.
  destruct (fill_cut m (a + 6128) (ms - 4096 - 16 - 2016) 16 0 Z2 ltac:(clear -MSR NSE RSR N; lia)) as [ZH Z3]. clear Z2.
  replace (a + 6128 + 16) with (a + 6144) in Z3 by lia.
  destruct (fill_cut m (a + 6144) (ms - 4096 - 16 - 2016 - 16) n 0 Z3 ltac:(clear -MSR NSE RSR N; lia)) as [ZU ZT]. clear Z3.
  replace (ms - 4096 - 16 - 2016 - 16 - n) with (ms - 6144 - n) in ZT by lia.
  pose proof (zeros16_hdr m (a + 6128) ZH) as HDR. clear ZH.
  destruct (c8c8_of_junk m (a + 4096) (fill_is_junk _ _ _ _ ZAB)) as (j1 & j2 & LH).
  (* [comment removed for export] *)
  rewrite SGN in SHZ, SHF2.
  destruct (fill_cut m (shad a + 512) (512 + granules n) 256 0 SHZ ltac:(clear -SG5; lia)) as [SHL S1]. clear SHZ.
  replace (shad a + 512 + 256) with (shad (a + 6144)) in S1 by (rewrite SG2; lia).
  destruct (fill_cut m (shad (a + 6144)) (512 + granules n - 256) (shlen (n - n mod 8)) 0 S1 ltac:(clear -SG5 SG6; lia)) as [SHU S2]. clear S1.
  destruct (fill_cut m (shad (a + 6144) + shlen (n - n mod 8)) (512 + granules n - 256 - shlen (n - n mod 8)) (granules n - shlen (n - n mod 8)) 0 S2
              ltac:(clear -SG5 SG6; lia)) as [SHP S3]. clear S2.
  replace (shad (a + 6144) + shlen (n - n mod 8) + (granules n - shlen (n - n mod 8))) with (shad (a + 6144) + granules n) in S3 by lia.
  assert (SHT : junk_at m (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n)).
  { replace (ms / 8 - 768 - granules n) with ((512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))) + (ms / 8 - 512 - (512 + granules n)))
      by (clear -SG5 SG6; lia).
    apply junk_merge; [apply (fill_is_junk _ _ _ 0); exact S3 | apply (fill_is_junk _ _ _ 0xfa) | clear -SG5 SG6; lia | clear -SG5 SG6 MSE MSM SGN NSE RSE N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
    replace (shad (a + 6144) + granules n + (512 + granules n - 256 - shlen (n - n mod 8) - (granules n - shlen (n - n mod 8))))
      with (shad a + 512 + (512 + granules n)) by (rewrite SG2; clear -SG5 SG6; lia). exact SHF2. }
  clear S3 SHF2.
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs m (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]).
  { intros NE. apply c1_of_fill; [lia|]. rewrite SGG in SHP. destruct (Z.eqb_spec (n mod 8) 0) as [E|_]; [exfalso; exact (NE E)|].
    replace (shlen (n - n mod 8) + 1 - shlen (n - n mod 8)) with 1 in SHP by lia. exact SHP. }
  clear SHP.
  rewrite <- SG1 in SHL.
  (* [comment removed for export] *)
  replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST, FRa by lia.
  (* [comment removed for export] *)
  eapply (allocBC_sec DI PR L RNG R k Q spA gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n (bv_unsigned sp + -2128) t a ms nsec SB lo sz 336752 tb tr fr0
            (Z_to_bv 64 0x31200) s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11).
  all: try lazymatch goal with
       | |- forall _, _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PMC
       | |- ADEPOT _ _ _ => exact DEP
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- u64arr _ _ _ _ => exact TB
       | |- _ \/ _ => first [unboxed DJSB | unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS | unboxed CT2]
       | |- exists junk, _ => exact SHT
       | |- ~ _ -> _ => exact SHP1
       | |- rw_cells _ _ (shad (_ + 4096)) _ => exact SHL
       | |- rw_cells _ _ (shad (_ + 6144)) _ => exact SHU
       | |- rw_cells _ _ (_ + 6128) _ => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR4
       | |- rng _ _ _ => solve_rng
       | |- is_primary _ = _ => exact PRIM
       | |- _ = sec_map_size _ => exact HMS
       end.
  all: try eassumption.
  all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI SB0 SBH CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 SZB S47 MSB ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
  all: match goal with |- forall _, _ => idtac | |- ?G => idtac "REMBC" G end.
  (* [comment removed for export] *)
  intros RNG' m2 id rax t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b s6b t3b t4b t5b t6b PB IDR.
  unfold allocBC_postS in PB.
  destruct PB as (id_ & raB & t0_ & t1_ & t2_ & a0_ & a1_ & a2_ & a3_ & a4_ & a5_ & a6_ & a7_ & s6_ & t3_ & t4_ & t5_ & t6_
                  & EMS & FPLE & MUb & WMb & MIb & STb & IDR_ & HDRb & SHFb & SHUb & SHPb & SHTb & DEPb & PCb & PMCb).
  clear EMS IDR id. rename id_ into id. rename IDR_ into IDR.
  rewrite ?HspA in MUb.
  replace (Z_to_bv 64 (a + 6128)) with (Z_to_bv 64 (a + 6144 + -16)) by (f_equal; lia).
  replace (a + 6128) with (a + 6144 + -16) in HDRb by lia.
  pose proof (hdr_b1_mid_range 0 ltac:(lia)) as B1M.
  assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
  assert (RIMG' : rng_aimg RNG') by (eapply rng_fp_le; [exact FPLE| exact RIMG]).
  assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX]).
  assert (RT' : rng RNG' t 4096) by (eapply rng_fp_le; [exact FPLE| exact RT]).
  assert (RA' : rng RNG' a ms) by (eapply rng_fp_le; [exact FPLE| exact RA]).
  (* [comment removed for export] *)
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; lia).
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(lia). xport TSD MUb WMb ltac:(lia).
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; lia).
  xport FLG MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia). xport MCS MUb WMb ltac:(lia). xport CF34 MUb WMb ltac:(lia).
  pose proof PCb as PC'. destruct PC' as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  assert (ZU2 : fill_at m2 (a + 6144) n 0).
  { eapply fill_frame; [exact ZU | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  xport FR16 MUb WMb ltac:(lia). xport SS MUb WMb ltac:(lia). xport FRS MUb WMb ltac:(lia).
  xport TB MUb WMb ltac:(rewrite LTB; lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs m2 (a + 4096) [C8 j1; C8 j2]).
  { intros _. xport LH MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia). exact LH. }
  clear LH.
  (* [comment removed for export] *)
  xport HDR4 MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  xport PGJ MUb WMb ltac:(ub DJN; ub DJS; clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2; dlia).
  assert (ZJ2 : fill_at m2 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (ZT2 : fill_at m2 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT | exact MUb | exact WMb |]. intros Hp. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 Hp SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb SG1 SG2. dlia. }
  assert (SHF12 : fill_at m2 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF1 | exact MUb | exact WMb |]. intros _. cbn [disjoint_from fst snd]. ub DJN; ub DJS.
    clear -HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Y Y0 N0 R0 SHB1 SHB2 MS8 MS6 ALO1 ASD ASDa ASDb NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI SG1 SG2. dlia. }
  clear ZU ZJ1 ZT SHF1 SHL SHU SHP1 SHT HDR HDRP.
  (* [comment removed for export] *)
  iprefix.
  eapply evtF_cut.
  { eapply (allocD_sec L RNG' spA gp tp F fc m2 n t (a + 4096) (a + 6144) lo 0 (hdr_b1_mid 0) id (bv_unsigned sp + -2128) sj
              (repeat (Z_to_bv 8 0) (Z.to_nat n)) j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => ub DJT; clear -Y N MSR NSE RSR; lia
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         | |- rw_cells _ _ (_ + 6144) [CB _ _] => exact ZU2
         | |- is_primary _ = _ => exact PRIM
         | |- _ = _ + rz_size _ => rewrite RZ; lia
         | |- _ mod 16 = 0 => clear -AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
         end.
    all: try eassumption.
    all: try (eapply ablk_sub; [exact ALO | clear; lia | clear -N MSR NSE RSR MSB; lia]).   (* [comment removed for export] *)
    all: try (rewrite ?HspA; unfold AIMG_HI; clear -HspA SPR CEIL LO N AAL ALO AHI CX0 CX1 CXS T0 T1 TS N0 N1 R0 R1 S47 MSB MSR NSE RSR B1M IDR ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb CBND CBNDa CBNDb; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_postG in PD.
  destruct PD as (t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m3 & sj3
                  & -> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  rewrite ?HspA in MUd.
  specialize (LHd ltac:(rewrite RZ; lia)).
  xport FR16 MUd WMd ltac:(lia). xport SS MUd WMd ltac:(lia). xport FRS MUd WMd ltac:(lia). xport TB MUd WMd ltac:(rewrite LTB; lia).
  xport HDR4 MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  xport PGJ MUd WMd ltac:(ub DJT; clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR RZ RSR NSE MSR ALO1; lia).
  assert (ZJ3 : fill_at m3 (a + 4096 + 16) 2016 0).
  { eapply fill_frame; [exact ZJ2 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR ALO1. dlia. }
  assert (ZT3 : fill_at m3 (a + 6144 + n) (ms - 6144 - n) 0).
  { eapply fill_frame; [exact ZT2 | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd]. ub DJT.
    clear -Y HspA SPR CEIL LO N AAL ALO AHI MSB MSR NSE RSR Hp ALO1. dlia. }
  assert (SHF13 : fill_at m3 (shad a) 512 0xfa).
  { eapply fill_frame; [exact SHF12 | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SHFb3 : fill_at m3 (shad a + 512) 256 0xfa).
  { eapply fill_frame; [exact SHFb | exact MUd | exact WMd |]. intros _. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SHB2 MS8 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (SGX : shad (a + 6144) + granules n + (ms / 8 - 768 - granules n) <= 0x10007fff8000 /\ 0 <= ms / 8 - 768 - granules n)
    by (rewrite SG2; clear -SHB2 SG9 MSR NSE RSE N; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  destruct SGX as [SGX1 SGX2].
  xport SHUb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs m3 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2; dlia). exact SHPb. }
  assert (SHTd : fill_at m3 (shad (a + 6144) + granules n) (ms / 8 - 768 - granules n) 0xfa).
  { eapply fill_frame; [exact SHTb | exact MUd | exact WMd |]. intros Hp. cbn [disjoint_from fst snd].
    clear -HspA SPR CEIL LO N ALO TS SHB1 SGX1 SGX2 SG5 SG6 Hp ALO1 ASD ASDa ASDb TBND TBNDa TBNDb MS6 MSB SG1 SG2. dlia. }
  assert (DEPd : ADEPOT DI L m3).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx; ub DTN; ub DTS; ub DJN; ub DJS; clear -Y Y0 Y1 Y2 Hx HspA SPR CEIL LO N AAL ALO AHI MSB MS6 T0 TS T1 N0 N1 R0 R1 ALO1 NBND NBNDa NBNDb NI SBND SBNDa SBNDb SI TBND TBNDa TBNDb; lia|]). apply Forall_nil. }
  assert (PCd : poison_cells m3).
  { eapply poison_cells_frame_b; [exact PCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  assert (PMCd : premap_cells m3).
  { eapply premap_cells_frame_b; [exact PMCb | exact MUd | exact WMd |].   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI, AIMG_LO; clear -HspA SPR CEIL LO T0 ALO ALO1; lia|]). apply Forall_nil. }
  clear SHF12 SHFb ZJ2 ZT2 ZU2 SHPb SHTb DEPb PCb PMCb.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 0x31200)) with (Z_to_bv 64 0x31200) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
  { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
    apply Z_to_bv_eqm. rewrite HspA. zeq. }
  rewrite EspA. rewrite HspA in STd. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in STd by lia.
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  eapply evtF_mono.
  { eapply (icptC_spec RNG' sp gp tp); [exact STd | atop_facts; lia | lia | exact MId | atop_facts; lia | exact FR16
      | eexists; split; [exact SS | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
      | exact FRS | exact RIMG' | solve_rng ]. }
  cbv beta. intros ms5 PCC. destruct PCC as (m5 & -> & MUc & WMc & MIc & STc).
  (* [comment removed for export] *)
  xport STATSd MUc WMc ltac:(exact I). xport HDRd MUc WMc ltac:(exact I). xport UFd MUc WMc ltac:(exact I). xport LHd MUc WMc ltac:(exact I).
  xport HDR4 MUc WMc ltac:(exact I). xport PGJ MUc WMc ltac:(exact I). xport SHUb MUc WMc ltac:(exact I).
  assert (SHP5 : n mod 8 <> 0 -> rw_cells bsegs m5 (shad (a + 6144) + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPd NE). xport SHPd MUc WMc ltac:(exact I). exact SHPd. }
  assert (F5 : forall A l v, fill_at m3 A l v -> fill_at m5 A l v).
  { intros A l v H. eapply fill_frame; [exact H | exact MUc | exact WMc | intros _; exact I]. }
  assert (DEP5 : ADEPOT DI L m5). { eapply (adi_frame DI); [exact DEPd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PCX5 : poison_cells m5). { eapply poison_cells_frame; [exact PCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (PMC5 : premap_cells m5). { eapply premap_cells_frame; [exact PMCd | exact MUc | exact WMc | apply Forall_nil]. }
  assert (MU : munch (mallocS_W L sp t a ms) m m5).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUc]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_weaken; [| exact MUb].
    all: unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA MSR NSE RSR N SG9 SG5; lia. }
  assert (WM : wmono bsegs m m5).
  { eapply wmono_trans; [exact WMb|]. eapply wmono_trans; [exact WMd| exact WMc]. }
  eapply KONT. unfold malloc_postS.
  split; [exact FPLE|]. split; [exact MU|]. split; [exact WM|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDR|].
  split; [exact STATSd|]. split; [exact LSJd|]. split; [exact HDR4|]. split; [eexists; exact PGJ|].
  split; [exact LHd|]. split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZJ3|].
  split. { change 17 with (Z.lor (Z.land (hdr_b1_mid 0) 243) 0). exact HDRd. }
  split. { rewrite skipn_repeat in UFd. exact UFd. }
  split; [apply (fill_is_junk _ _ _ 0); apply F5; exact ZT3|].
  split. { change 768 with (512 + 256). apply fill_merge; [apply F5; exact SHF13 | apply F5; exact SHFb3 | lia | lia]. }
  split.
  { unfold block_shadow_bytes. rewrite SGS, SGG.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
    - rewrite app_nil_r, Z.add_0_r. exact SHUb.
    - lazymatch goal with |- rw_cells _ _ _ [CB _ (?l1 ++ ?l2)] =>
        replace (Z.to_nat (shlen (n - n mod 8) + 1)) with (Z.to_nat (shlen (n - n mod 8)) + 1)%nat by (clear -SG5; lia) end.
      apply cb_app2; [exact SHUb|]. rewrite Z2Nat.id by (clear -SG5; lia).
      eapply rw_cells_recast; [exact (SHP5 M0) | cbn; tauto | reflexivity | reflexivity]. }
  split; [apply F5; exact SHTd|].
  split; [exact DEP5| split; [exact PCX5| exact PMC5]].
  Unshelve. all: try exact STb; try exact ST.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
(* [comment removed for export] *)
