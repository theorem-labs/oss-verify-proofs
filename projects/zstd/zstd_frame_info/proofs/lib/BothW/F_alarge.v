(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase ABytes AKit AKit2 AKitQ AModelFacts APrimFacts ASecFacts ASecSlog RT_stubs ARep ARepKit
     F_memset F_apoison F_apoison0 F_aalloc3 F_acache3 F_ammap F_ammapz.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition large_entry := 0x3599c.
End CANSEC1.
Notation LARGE_STACK := 464 (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
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
Definition large_cells (ctx t PA : Z) (m : amem) : Prop :=
     rmap_cells m /\ poison_cells m
  /\ rw_cells bsegs m 0x98ff8 [C8 (Z_to_bv 64 0x9aed0)] /\ rw_cells bsegs m 0x9aed0 [C8 (Z_to_bv 64 0x191d0)]
  /\ rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)]
  /\ rw_cells bsegs m 0x9da18 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)].      (* [comment removed for export] *)

#[using="Type"] Lemma large_cells_frame : forall ctx t PA m m' W, large_cells ctx t PA m -> munch W m m' -> wmono bsegs m m' ->
  AIMG_HI <= ctx ->
  Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv))      (* [comment removed for export] *)
                    \/ (0x9da30 <= fst iv /\ snd iv <= 0xa0240)) W -> large_cells ctx t PA m'.
Proof.
  intros ctx t PA m m' W LC MU WM CX HW.
  destruct LC as ((Q1 & Q2 & Q3 & Q4 & Q5) & (P1 & P2 & P3 & P4 & P5 & P6 & P7) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  unfold AIMG_HI, AIMG_LO, ATP88, ATSD in *.
  assert (D : forall A k, 0 <= k -> ((0x10000 <= A /\ A + k <= 0x9da30) \/ (0xa0240 <= A /\ A + k <= 0x5f6000) \/ (A = ctx + 152 /\ k = 8)) -> disjoint_from W A k).
  { clear -HW CX. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>14065007797.3222827330037.3228350488757.3229700517941.3229769726197.3230126708405.3230296331679.1333666907028.3234967449077.3237062828469.3239922301493.3244116026549.3244669382197.3251614005557.3255695965749.3256910195381.3258692149.32   64336869237.3268060973103.3200000100200300400500600@00A00B00C00D00E00F00G00H00I00J00K00LSSSSSSS2CX2HA2H1SSSSSSSSSSSS".
split; [lia| apply IH; assumption]. }
  unfold large_cells, rmap_cells, poison_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | unfold ATP88, ATSD; cbn; apply D; lia]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma zeros32_hdr : forall m A, fill_at m A 32 0 ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells bsegs m 0x9dc80 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x9dc80 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=38834543651.557022093363.560302399878.5000004005006S2HbSS".
replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells bsegs m 0x9dc80 [C4 (Z_to_bv 64 b)] ->
  rw_cells bsegs m 0x9dc80 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=38834543651.557022093363.560302399878.5000004005006S2HbSS".
replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition large_post (RNG : footprint) (sp : word) (a n ctx t PA nres nsec nres' lo : Z) (m : amem)
    (RNG' : footprint) (m' : amem) : Prop :=
  let size := needed_size n in let ms := sec_map_size n in let res := a + 4096 in let ue := res + size in
     fp_le RNG RNG' /\ fp_bw RNG'
  /\ a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP            (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
            (AINSTANCE + 112, AINSTANCE + 720); (t + 2800, t + 3168);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres')]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                          CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))]
  /\ rw_cells bsegs m' res [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))]
  /\ fill_at m' (shad a) 512 0xfa
  /\ fill_at m' (shad a + 512) (size / 8) 0
  /\ fill_at m' (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa
  /\ rng RNG' a ms /\ rng RNG' (shad a) (ms / 8)
     (* [comment removed for export] *)
  /\ rw_cells bsegs m' 0x9da48 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
  /\ rw_cells bsegs m' 0x9da58 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0x9da60 32 /\ junk_at m' 0x9da80 512
  /\ rw_cells bsegs m' 0x9dc80 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0x9dc98 16
  /\ (exists sj', u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)]
  /\ ((nsec <> nres /\ nres' = nres)
      \/ (nsec = nres /\ nres' = nres + 16384
          /\ rw_cells bsegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]
          /\ rng RNG' (PA + 8 * nres) 131072))
  /\ nres' <= 1048576
  /\ large_cells ctx t PA m'.

(* [comment removed for export] *)
#[using="Type"] Lemma c8x4_of_junk : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells bsegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  destruct (c8c8_of_junk m A J1) as (w1 & w2 & H1). destruct (c8c8_of_junk m (A + 16) J2) as (w3 & w4 & H2).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app bsegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lxor63 : forall k, 0 <= k <= 63 -> Z.lxor k 63 = 63 - k.
Proof.
  apply (range_by_compute (fun k => Z.lxor k 63 = 63 - k) (fun k => Z.lxor k 63 =? 63 - k) 0 63); [| vm_compute; reflexivity].
  intros z Hz. apply Z.eqb_eq. exact Hz.
Qed.

(* [comment removed for export] *)
Definition large_tail_post (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (a ms size PA nres' nsec lo : Z) (fj : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 sp0) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom bsegs)
    /\ munch [(sp0 - 96, sp0); (a + 24, a + 32); (0x9da48, 0x9dca8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo sp0
    /\ rw_cells bsegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)]
    /\ rw_cells bsegs m' 0x9da48 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
    /\ rw_cells bsegs m' 0x9da58 [C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0x9da60 32 /\ junk_at m' 0x9da80 512
    /\ rw_cells bsegs m' 0x9dc80 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0x9dc98 16
    /\ rw_cells bsegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].

#[using="Type"] Lemma large_tail_spec : forall RNG (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a ms size PA nres' nsec k lo : Z) (srt : byte) (fj jstats jbsl jglob jslot : list byte),
  stk bsegs m lo (sp0 - 96) -> ATOP <= lo -> lo <= sp0 - 96 -> sp0 < 2^64 ->
  mem_inv bsegs m ->
  rw_cells bsegs m (sp0 + -96) [CB 8 fj; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells bsegs m 0x9da18 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x9da48 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0x9da58 [C1 srt] ->
  rw_cells bsegs m 0x9da60 [CB 32 jstats] -> rw_cells bsegs m 0x9da80 [CB 512 jbsl] ->
  rw_cells bsegs m 0x9dc80 [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m 0x9dc98 [CB 16 jglob] ->
  rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot] ->
  ablk a (a + ms) -> a + ms <= ATOP -> (a + ms <= PA \/ PA + 8388608 <= a) ->
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> 0 <= nsec -> 8 * nsec + 8 <= 8388608 -> 0 <= nres' < 2^64 ->
  73728 <= ms <= 536821760 -> 34 <= k <= 47 ->
  rng_aimg RNG -> rng RNG lo (sp0 - lo) -> rng RNG a ms -> rng RNG (PA + 8 * nsec) 8 ->
  evtF bsegs RNG (large_tail_post sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 F fc a ms size PA nres' nsec lo fj m)
    (MS (mkR ra (Z_to_bv 64 (sp0 + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0x9dc88) (Z_to_bv 64 0x9da18) a0 a1 a2 (Z_to_bv 64 nsec) a4 a5 a6 a7
             (Z_to_bv 64 ms) (Z_to_bv 64 k) s4 (Z_to_bv 64 a) s6 s7 s8 s9 s10v s11v t3 t4 t5 t6)
        F (Z_to_bv 64 0x35c00) fc None m (seg_rom bsegs)).
Proof.
  intros until jslot. intros ST CEIL LO SP64 MI FR I64 ZH INS SRT JST JBS MTX JGL JSL AHI ACE DAP PA0 PA1 NS0 NS1 NR MSB KB RIMG RSTK RCH RPS.
  pose proof AHI as AHI0. pose proof PA0 as PA00. clear AHI PA0. destruct (ablk_int _ _ AHI0) as (kA & AHI & AHIa & AHIb & AHIc & AHId). destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).   (* [comment removed for export] *)
  atop_facts.
  pose proof (munch_refl [(sp0 - 96, sp0); (a + 24, a + 32); (0x9da48, 0x9dca8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  box DAP.
  destruct (c8_of_junk m (PA + 8 * nsec) (ex_intro _ jslot JSL)) as [wj PAS]. clear JSL.
  step.                                                        (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0360?10743075417.11610862073820.11810902445684.12111424881535.12911799361125.11212010938993.11912053063107.2  12121701742.2  12300957722.1201256740996.129 12589007235.12013168802263.16 132947688.118  13584623497.11714149018477.12114361274672.11814507198897.12714714734196.12114852231924.12114966475568.12215342322172.12415342322175.12515675919530.1  1607211312.122 16388449056.1291720665713.115 18459507890.10618631400196.11718661153180.1231869417598.0   18922343167.12219438934449.12719773085812.12120189023920.12920567197315.12020645452976.12920713082244.12920748863107.12020840460404.12120977358580.12121189826028.12722551848964.11723077509607.12623217243312.12923283716588.1272434767853.128 24402725564.12125220224756.12125737879428.12925757466715.12125856448160.11725950461401.12827050862559.11427445073329.12527580019444.12127975202284.12728768091006.12628800268228.12929282142829.11229297447021.11229737134219.12929993300557.11930498642920.12131000663539.12331153249960.1  3119189552.121 31790753535.12532356565379.12032729252332.12733100000457.12333183383216.1293360343661.117 33982388067.1  34070237940.12134117777903.1293418254762.127 34509919194.1083515988228.117 35305913430.2  36264551952.12137523538307.12037625410381.12138056291523.12438779560496.1213894609928.111 39005674622.12639188636933.0  39332637397.0  39453804551.11239453804551.11739453804551.11839453804551.12039453804551.12139453804551.12239453804551.12739453804551.12939934446001.1264050905771.1   40610480139.12940735080004.11740773122600.12741132673840.11841545695612.1244189464191.125 41895735382.11042061375533.12342147983920.12142167927917.12042974364865.1244377449905.126 44408093901.12744652134833.12644669337020.11845964270975.12546126211376.11846194827934.11246983758296.11847392702768.12247856399731.11747898542384.11848148872177.1274816657503.121 48512012420.12948725199152.12248773843565.11249734414896.1215010566057.117 50425481805.1165152994737.125 51995846275.12052078938469.1  53130415725.11253296086404.12953586308484.129541565951.129  54179311471.11754560324002.11654564293424.11854568455164.12454634654724.11754650817328.12254693945639.1275476079548.122 55060268159.12255295209076.12155656648323.12055664284081.1265612563248.122 5627157937.125 5627157937.126 56420612883.11856464009520.11856747988284.12057002388212.12157072143507.12957511931568.12957806795312.12158049312993.4  58358549779.12259331759635.12159796477325.2  60445238764.12761341932720.12961570494580.12161588179377.12561897234907.12161982047565.12062454858145.0  62995630236.16 63121334769.11963225022824.12963282490989.11263285576040.12563884813933.11264448714349.11264673700584.12264806989052.12465447523820.12766124323454.12666861428735.12566989559971.12767256234740.12167475915206.11368089342980.11768157851057.12768267961481.1207129386719.121 7250812425.120 7457385550.2   7847713540.117 8374386292.121 8445983548.129 884720176.121  8862146960.121 8965918046.119 9050768876.127 9583930681.1   9717231777.0   00000100500600?00@00A00E00I00J00N00\00k01101201301401501601701801<01@01A01B01L01M01Q01R01S01T01]01^01_01`01n01o02002>02?02E02N02O02S02T02]02^02h02i02j03303=03>03?03@03A03J03N03T03Z03`03i03j04004904:04;04?04M04V04W04X04Y04Z04[04f05405905:05>05H05V05Z05[05\05`05d05e05f05g05h05i05j05k05l06M06N06O06P06Y06_07107207607:07@07A07B07C07D07E07F07G07Q07U07V07h07l07m07n07o08008;08<08=08C08D08E08F08G08U08V08\08]08^08g09209309409809909=09P09Z09c09d0:20:30:40:50:60:A0:B0:X0:Y0:d0:e0:f0:g0;20;=0;A0;J0;K0;L0;M0;V0;W0;X0;g0;h0;n0<40<80<>0<D0<J0<N0<W0<[0<_0<`0<d0<m0<n0<o0=00=;0=<0==0=>0=D0=N0=O0=Y0=]0=f0=g0=hSS2LOSS2KB4HBSBSSS2KBS2KBSS2KBS3NS03HPS4PA0aS3NS03NS13MSB1YS4AHIaSSSSSSSS2LOS2LOSSS3NS04PA0aSS2KBSFSS2KB4HBSBSSSS3NS03HPS4PA0aSSS3NS03HPS4PA0aSS4AHIaS2KB4HBSBSS2HBSS2KB4HBSBSS3NS04PA0aSSS2KB4HBSBS3NS04PA0aSFSSS2KB4HBSBS2LOS4AHIaS4AHIaS4AHIaS2KB4HBSBSS4AHIaS2KB4HBSBSSS2LOS3NS03HPS4PA0aS2KB4HBSBFSSSSS4CEIL2LO1HS2KB4AHIa4HBSBS3MSBSS2KBS3NS04PA0aS3NS03HPS4PA0aS2KBSSS2HBS2LOSSSSSSSSS4CEIL2LO3NS02KB4AHIa4PA0a1H4HBSBSSSS2KB4HBSBS4AHIaS3NS02KB4PA0a4HBSBSS2LOS2LOS4AHIaFSSSSSSS3NS04PA0aS2LOSS4CEIL2LO3MSB4AHIdS2HBSSSSS4CEIL2LO1HSSS4AHIaSSSSS3NS03HPS4PA0aSS4AHIaSSS2KB4HBSBS4CEIL2LO1HSSS2LOSS2KBS4CEIL2LO2KB1H4HBSBS3NS04PA0aS2KB4HBSBSS3NS03HPS4PA0aSSSSS4CEIL2LO1HSS4CEIL2LO3NS13HPS4PA0dSS4CEIL2LO1HSSSS4CEIL2LO1HS4CEIL2LO1HS2KBS2KB4HBSBSSSS2KB4HBSBSSS3NS03NS13MSB1YSS4AHIaS4AHIaS2HBS4AHIaS4AHIaS4AHIaS2LOS2KB4HBSBS2LOS2LOSS2KBS3NS03NS1SSSS4CEIL2LO1HSSSS4AHIaS3NS04PA0aSS3NS04PA0aS2HBS2KB4HBSBSS".
zstep. rewrite (lxor63 k) by (clear -KB; lia).               (* [comment removed for export] *)
  box PAS. snapshot [(a + 24, a + 32)]%Z MUh WMh.
  step.                                                        (* [comment removed for export] *)
  carry PAS MUh WMh ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUh WMh.
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NS0 NS1; lia).
  box ZH. snapshot [(PA + 8 * nsec, PA + 8 * nsec + 8)]%Z MUp WMp.
  remember (PA + 8 * nsec) as PS eqn:HPS.
  step.                                                        (* [comment removed for export] *)
  subst PS.
  carry ZH MUp WMp ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUp WMp.
  (* [comment removed for export] *)
  destruct (c8x4_of_junk _ 0x9da60 (ex_intro _ jstats JST)) as (w1 & w2 & w3 & w4 & AST). clear JST.
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (junk_split _ 0x9da80 (8 * (63 - k)) (512 - 8 * (63 - k)) ltac:(replace (8 * (63 - k) + (512 - 8 * (63 - k))) with 512 by (clear; lia); exists jbsl; exact JBS)
              ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as [JB1 JB2].
  destruct (junk_split _ (0x9da80 + 8 * (63 - k)) 8 (512 - 8 * (63 - k) - 8) ltac:(replace (8 + (512 - 8 * (63 - k) - 8)) with (512 - 8 * (63 - k)) by (clear; lia); exact JB2)
              ltac:(clear; lia) ltac:(clear -KB; lia)) as [JBW JB3]. clear JB2 JBS.
  destruct (c8_of_junk _ _ JBW) as [wb BSL]. clear JBW. destruct JB1 as [bs1 JB1]. destruct JB3 as [bs3 JB3].
  remember (0x9da18 + 8 * (63 - k)) as BSB eqn:HBSB.
  replace (0x9da80 + 8 * (63 - k)) with (BSB + 104) in BSL by (subst BSB; clear; lia).
  replace (0x9da80 + 8 * (63 - k) + 8) with (BSB + 112) in JB3 by (subst BSB; clear; lia).
  step. if_cases KM; zify_cond KM.
  all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x35c44) _ _ _ _) => step end.   (* [comment removed for export] *)
  all: zstep; zstep.                                           (* [comment removed for export] *)
  all: setreg 11 (Z_to_bv 64 BSB) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); subst BSB; clear -KB; lia).
  all: step.                                                   (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: destruct (c8c8_of_junk _ 0x9dc98 (ex_intro _ jglob JGL)) as (g0 & g1 & GL); clear JGL.
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0x9dc98) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0x9dca0) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: apply (mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: do 13 step.                                             (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells bsegs ?mm (?spz + -96) (CB 8 _ :: _) |- _ => lazymatch goal with STK : stk bsegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; unfold large_tail_post; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact ZH|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact (junk_of_cells _ _ _ AST)|].
  all: split.
  1,3: subst BSB; replace 512 with (8 * (63 - k) + (512 - 8 * (63 - k))) by (clear; lia);
       apply junk_merge; [exists bs1; exact JB1 | | clear -KB; lia| clear -KB; lia];
       replace (512 - 8 * (63 - k)) with (8 + (512 - 8 * (63 - k) - 8)) by (clear; lia);
       apply junk_merge; [ | | clear; lia | clear -KB; lia];
       [ replace (645760 + 8 * (63 - k)) with (645656 + 8 * (63 - k) + 104) by (clear; lia); exact (junk_of_cells _ _ _ BSL)
       | replace (645760 + 8 * (63 - k) + 8) with (645656 + 8 * (63 - k) + 112) by (clear; lia); exists bs3; exact JB3 ].
  all: split; [assumption|]. all: split; [| assumption].
  all: exact (junk_of_cells _ _ _ GL).
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma large_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0x9da18 -> a1 = Z_to_bv 64 0x9dc88 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9da48 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0x9da58 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells bsegs m 0x9da60 [CB 32 jstats] ->
  rw_cells bsegs m 0x9da80 [CB 512 jbsl] ->
  rw_cells bsegs m 0x9dc80 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x9dc98 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells bsegs m (PA + 8 * nsec) [CB 8 jslot]) ->
  (PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  AIMG_HI <= ctx -> iclr t 4096 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall a, FRESH a = true ->
        ablk a (a + ms)
     /\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
     /\ fill_at m (shad a) (ms / 8) 0) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
      implS bsegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS bsegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS bsegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS bsegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS bsegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  pose proof PA0 as PA00. clear PA0. destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, large_entry in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  set (size := needed_size n) in *. set (ms := sec_map_size n) in *.
  (* [comment removed for export] *)
  box STATS. box INS. box SRT. box JST. box JBS. box MTX. box JGL.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0;M0?10026074842.25210145486483.22 10280110829.26610653515994.25210655732660.25810864281461.64 10864281461.65 11424805613.2661149840136.0   11499002610.24711566666413.4  1162083375.125 11774978335.26411799361125.12711799361125.12811799361125.12911799361125.13011799489570.25211821014900.2931188899058.247 11991125079.32 12099830708.25812178473528.54 1230333318.64  1230333318.65  12322440645.4  12358518976.12812428150072.23112430247196.24812438755220.25 12438755220.26 1261375960.212 1261375960.260 1261375960.261 1261375962.257 1275541697.267 12870277089.64 12870277089.65 12872509567.52 12872509567.53 12992780212.25813159172246.5  13313577562.3  13503541744.35 13607424500.29313700146930.2471370718544.2   1374799060.20  13892155040.45 13917980321.0  13918739985.20 14040914212.25814043218912.24714195269059.52 14195269059.53 14618011854.24814620109034.23115038864242.24815041073143.24615041134720.24715041903002.10 15223532909.26815369618241.2671538918798.32  15466193844.25815547824852.47 15551743849.46 15552591796.25815656081280.17 15666453319.24915668550499.2321602526669.33  16148322415.24616189233663.18 16261547890.24816361892545.26716709567841.3  16804761832.3  16831639642.3  1696159597.268 17151130279.12717210349934.2  17298323393.26717318890361.55 17318890361.56 17427450631.24817429547811.23117511488259.24917538010112.24817538300399.29317542202648.24717559379343.18 17594417445.15 17638902509.2661773310350.26  17764507885.26617776320431.12517807136772.2461785468898.3   17896243954.24717928946626.17 17986879152.10 17986879152.15 17986879152.20 17986879152.26 17995455655.12618155678445.2661820345069.266 18361259584.12718422146077.20 18527123682.52 18527123682.53 18548796306.23218577301697.26718802973426.24718911120308.25818913870613.6  18918200149.24718930958230.20 18973537268.29319042827563.12819092398759.1261927430893.266 1937063194.15  19617313304.11 19617313304.15 19617313304.24 19617313304.27 19617313304.35 19670594045.24719844650349.26819885335399.10 19885335399.52 19885335399.53 19970277031.12620163737475.12520218225962.52 20218225962.53 20243403444.25820269398461.55 20269398461.56 2047665247.64  2047665247.65  2050035067.260 21001671296.17 21193855476.29321227682692.33 2124193155.126 21284799705.25 21284799705.26 21362561773.26621472669832.8  21546765645.17 21897047577.44 22214649138.24522664701128.4  22706555394.6  22922673522.2482295126554.4   23092036546.33 23386168314.18 23627005501.32 23726270554.25223770140939.3  23881951450.25223891548451.23223893645575.2492400638038.22  24052312410.25224147499556.26624189958221.17 24275854194.24824344800858.25224360031986.24724380253120.12524436996044.3  24482110322.24824880865951.2  24944995058.24725073974703.24825073974703.24925076071819.23125076071819.23225080282415.24725080282415.24825081078602.32 25082201984.17 25403042228.2582546492594.268 25527905671.24825530002851.23125535372424.26525557086848.17 25692740020.25825792348067.23125794445191.24825878270254.12626043255533.26626067558649.33 26370053044.25826390950137.33 26486114056.26726502771472.24726502771472.24826591984865.52 26591984865.53 26685873759.24626730776422.15 2713914275.232 27147338155.1272716011399.249 27462345696.26327574660128.25227776532267.2  27930427264.17 28028798645.4  28041173313.26728072922155.12928109204338.24828256979826.24828370640551.12528450832218.2  2845652246.228 28712180082.24828735343981.26828764920455.24828767017635.23129067115679.19 29293392732.4  2937190991.27  29406937538.33 2943433837.268 29693610996.29329784318686.2  29875836246.26629894763890.24830008181843.10 30078181876.7  30196666605.26630414451008.12730521169266.248305622464.128  3059552449.267 30770604737.26730797285812.25830805812953.25 30805812953.26 31012612437.0  31026020490.37 31026020490.38 31049611629.26831161366443.12831191324469.4  31613213566.3  31649644204.5  31853783632.24831865172116.26131872282082.3  31929422313.14031936348496.5  32005092028.22 32023300461.26832127996803.12632310233831.37 32310233831.38 32615709421.2663263951075.3   32855991661.26832907263168.12732938500103.55 32938500103.56 33022739650.17 33062543571.20 33062543571.26 33623804571.17 33764744995.23233766842119.24933793008176.4  33890036527.12533949364657.24834164772537.6  34169364217.24734241467122.24734326450181.3  34330730127.10 34354335075.3  34374882658.26534398147309.2663445593421.17  34468826361.33 3457088893.248 34690630551.5  34791059821.26834885248674.26835051326972.6  35115460349.26 35205357699.12635209714819.12635269230345.29235340120754.26635367543687.24835369640867.23135435756793.33 3549109172.258 35637039136.21235876479702.26435998161932.22 35998161932.37 35998161932.38 36115622446.12636180999398.11736254144242.24736370756978.24836379156110.7  36493024877.26836651720741.20 36663969005.26636757669945.3  37003883527.24837005980707.23137144441050.25237428576193.26737457619906.17 37471900397.26637870397377.2673795062108.2   3799266425.1   38017335060.26638047397825.37 38047397825.38 3804798932.259 3804798932.260 38217320306.2483832836837.11  38498908914.24738692635477.0  38873630832.6  38965490467.1  3898508226.33  39012636437.0  39188636933.0  39191101890.17 39332637397.0  39378986105.26439661661252.4  40084807026.20 40091925676.12440150930599.12640240917767.24840240917767.24940241649863.24840243014947.23140243014947.23240243747043.23140505884423.24840507981603.23140600263088.3  40832288750.26840834385893.26740834385896.26440844629577.2574099768474.252 4104930669.268 41270082071.37 41270082071.38 41272171651.12741408184389.26741408184390.26641408184392.26441410281550.26841476191879.2  41526574044.20641536595426.10 42050527682.33 42132986300.32 42248457998.7  42250564277.21342250564277.23042250564277.24742263341421.2684237141073.27  42501170177.8  4259745615.25  4259745615.26  42727858484.25842803642915.24842805740039.23142887904618.12 429452623.25   429452623.26   42962563821.26643061792653.11543121191467.12943308111674.3  43358680699.4  4339538087.127 43399975277.32 43467924127.4  43624396838.37 43624396838.38 43786047718.18 43786047718.19 43803651437.26843831372141.26843885339585.26743987951406.12644002291905.26744007240616.26444009337774.268440101998.1    44487020397.25244572497956.5  44582905172.3  44611301484.3  4471461639.248 4473558819.231 44814614400.17 44892358593.26744960421824.12744969155572.29345235952922.25245456000882.24845486878294.35 45491065834.63 45656729165.25 45656729165.26 45912147617.0  45980917854.5  46084819894.26 46219515605.1  46268275148.34 46268275148.38 46361534285.17 46481087529.24746485146729.6  46932921792.33 46953039917.24747029806450.24847077701064.24747085737157.23447171318721.26747173633460.2584721740417.34  4721740417.38  47521462465.26748148872177.25648321848473.63 48366989682.24848637948928.17 48688118565.10 48706549617.29148721597440.26448721597453.26748723694598.26848729649807.25348729650694.13048956220434.45 49081353231.26349082866238.19 49089206181.25749111512429.26849125819610.25249220452722.2484923662446.6   49421114917.2  49422484845.26849425192486.15 49486495821.25 49486495821.26 49669356060.37 49669356060.38 49819069809.20 49940538093.26650085274403.23150087371527.24850131542183.12550189134306.7  50330077073.20 50495834861.26650516153480.0  50534541042.24750545063073.0  50586667242.54 50600290453.52 50600290453.53 50664164139.1295072571819.128 5079168823.0   50825812404.25850951108008.55 50951108008.56 50977580352.12651074778349.26651095978298.4  5114850435.127 51234361003.12851463134298.25251678667180.12451789176154.25251862169588.24651903217332.25852074235542.21052151318827.12652197829229.26852319338946.33 52523015483.26352575291859.24752575291859.24852577538839.25852577538839.26652577538839.26752577538839.26852577538839.29352844818625.26752846327745.26752877258371.3  52893039554.17 52978530989.24853028877591.4  53184632406.26253223416603.33 53257845651.20 53322291235.23253324388359.24953380534125.26853478231405.26853508216722.21053677435634.24753767577775.12553847904128.17 53870483715.4  53926293342.25 53926293342.26 54110583096.8  54142741234.24754455947213.17 54480643220.26854959380579.23254961477703.24955102181812.25855504905889.0  55534725313.26755737902772.25856170256219.21256170256219.22956170256219.24656174447011.7  56179074418.24856765693369.24656765693885.19856771238972.21256773336117.2095685972608.17  56980320960.1285703377594.20  5757267021.17  57579960569.33 57628698627.11 57628698627.6  57628698627.8  57699555840.10 57701672254.24757701672383.24657709577267.23457709577278.20657740518026.10 57765562098.24757885813324.24858143249301.2  58249443405.17 58280590976.17 58301326976.17 58342580660.2585867961120.37  5867961120.38  59048690994.3  59052983343.4  59192637571.12459264285594.25259308628179.8  59308629082.4  59314873579.11 59314873579.8  59384361202.24759586081466.26659588178609.14259723945897.22 59753510971.52 59753510971.53 59825920688.24759903583602.24859994940353.2676033954290.247 60544857842.24760759099917.7  60824532978.24761208149259.3  61305990311.12461539547572.25861560206755.23161562303879.24861779215085.26661853468551.24961855565731.2326187775056.51  6188023235.52  61917199023.12562083673382.22 62128165194.18 62128165194.19 62134644830.55 62134644830.56 6222207924.258 62232972069.20 62232972069.26 62250799188.23062252498992.4  62302209411.12662388333786.25262885933440.4  62892351972.23062999281728.12663006859994.25263049147592.23063063700652.4  63068058720.64 63068058720.65 63115510642.24863235321900.12363348234032.24863375992104.26463378089262.2686341393216.127 63480717402.25263607750905.33 63794685976.26763800006509.26863869911540.29363922752810.23063937043790.6  63972618880.17 64022359336.38 64307517712.29364342530482.26864543413632.17 64674898864.3  64725640282.25264760278381.26864772824451.12564875830376.7  64982457282.33 65095166637.22 65106454934.13065128844401.26 65212743211.12865344174682.25265461586437.2  65483078362.25265507993774.26865510090920.26465566963629.1  65778736149.37 65778736149.38 65809644506.25265914209601.26766022786591.52 66022786591.53 66119730114.33 66260595083.6  66295562989.26666336522568.6  66360475122.24766400036290.17 67105517212.24967229123954.24867381608175.19 6744704702.268 67466105445.2576746801845.267 6746801847.265 6746801848.264 67475915204.26867532237250.17 67567392795.4  67669709042.24767680999037.14067800019075.12767818022492.25767820119639.2606798355636.18  6798355636.19  68035828615.24968037925795.23268254437966.20 68254437966.37 68254437966.38 68311500677.17 68317042083.23168319139207.24868459412729.33 68634638273.2676875683698.248 7130566823.126 7203867998.25  7203867998.26  7486304935.127 7611240667.7   7654287582.264 7989643354.252 8265267294.0   848608446.258  848608446.266  848608446.267  848608446.268  8595948977.142 8603416747.127 8606889364.25  8606889364.26  8806422860.11  8806422860.12  8806422860.13  8806422860.8   8806422860.9   8935173664.270 8935173666.268 8937270825.267 8937270827.265 9197910491.6   9260898034.247 9264249647.258 9405922541.266 9638965854.247 9829218171.261 00000?00L00R00a00b01V02J02P02Q02Z02[02_02`02a02b02c02d03<03B03K03Z03[04A04P04_04`04d04e04f04l05205A05P05_05n06406Z07@07A07B07C07L07M07o08008908>08F08i08j08n08o09009109209a0:L0:U0:Z0:_0:d0:j0;00;10;20;30;40;50;;0;a0<40<50<:0<?0<H0<N0<S0<X0<Y0<_0<`0<a0<g0=J0=m0>S0>f0?T0?Y0?d0?i0?n0@20@80@@0@F0@J0@K0@P0@Y0@d0@j0A00A60A<0A=0AC0AI0AM0Ad0Ae0Af0BH0BN0BW0BX0BY0BZ0B[0B\0Ba0Bb0Bh0Bl0Bm0Bn0Bo0C00C10C=0CC0CR0DY0E`0Ea0Eb0Ec0Ed0Ee0FS0GA0H70Hm0I20I80I90IG0IH0IZ0Il0J20J30J>0J?0J@0JA0JE0JN0JS0J^0Jh0K70KF0KK0KZ0Km0LS0Lh0M70M;0MF0MO0M^0Mg0Mk0N00N90N:0NC0O_0PE0QJ0R40R50R60RH0RN0RO0RP0S60SI0SM0SS0ST0Sg0TM0TQ0TW0Ta0Tb0Tl0U00U10U20U30U40U90U>0UQ0UV0V<0VA0VB0VC0VI0VR0VX0V]0Vf0Vo0W00W10W20W;0WA0Wg0X:0X?0XD0XW0Xb0Xh0Xi0Xj0Xn0Y70Y80YA0YG0YK0YT0YX0Y^0Yd0Ye0Z70ZI0ZJ0Zi0[H0[N0[S0[T0[Y0[g0[h0[i0[n0\<0\E0\W0\]0\^0]80]R0]X0]]0]c0]g0^E0^c0^n0^o0_00_>0_Q0`70`80`<0`=0`>0`?0`H0`M0`R0`W0`[0`a0`l0a60aB0aH0aN0aO0aX0b70b80b90b:0b;0ba0c40c>0c?0cN0cR0c^0cj0d60d:0d;0dD0dM0dN0dT0dX0d^0dc0eI0e\0ek0f10f<0fB0fH0fI0fJ0f\0fa0ff0fk0fl0g50g;0gD0gE0gF0gG0gR0gS0gT0g_0g`0ga0gf0h20h60h70h]0iC0ii0j<0jO0jb0kH0k[0k`0ka0kb0kc0kd0l30l90lX0m70m80m90m:0m;0m<0mA0mP0m^0mi0n;0nJ0n\0nn0o@0oF0o_0oj0ok0ol10210310410B10C10D10J10N10S10T10Z10[10e10m11>11O11T11Y11_11e11k11o12512612712812912:12?12@12f13913?13E13I13J13Y13b14714L14[14j14k15315815915C15M15X15l15m16?16L16U16f17717=17>17P17h17n17o18e18n19419819919>19C19H19M19R1::1:D1:N1:X1:^1:m1;61;71;<1;B1;G1;V1;e1<<1<S1<_1<e1=81=^1=_1=`1=a1=g1=h1>11>21>`1>h1?01?51?:1?;1?<1?j1@X1@\1@b1@g1@h1@m1A<1A@1AO1AP1AQ1AR1AW1A]1Ah1Ai1Aj1Ak1Al1B11B61B;1B<1BB1BH1BO1BZ1Bg1Bn1C31CH1CI1C\1DB1DH1DN1DO1DX1D\1Db1Dc1E21EA1EB1EK1EL1E^1F11FW1FX1FY1F_1F`1Fe1Fj1Fo1G01G91GH1GW1Gf1H51H;1H?1HI1HT1H^1Hf1Hj1I21IC1I_1J;1JW1K31KB1KK1KL1KM1KX1K^1Kd1Ke1L?1LY1L^1Le1Lf1M51M=1ME1MT1M[1Md1Me1Mf1Mi1Mj1Mk1N11N:1N@1NI1NR1NS1N\1Na1Nb1Nc1O61O\1Ob1PH1P[1P\1P]1Pa1Pm1Q11Q51Q:1Q?1Q@1QD1QH1QI1QJ1QK1QZ1Q[1Q\1Q`1Qo1R01R11Re1SS1S\1S`1Sf1Sg1Sh1Sl1T;1TE1TW1T]1T^1Tn1To1U51UH1UR1US1UY1U^1Um1V31V41V:1VE1VH1VV1VW1V\1Vk1Vn1W=1W>1W?1W@1WE1WJ1WY1W_1W`1Wa1Wl1Wm1X31X41X=1XH1XI1XR1X^1X_1Xh1Xi1Xj1Xk1Y41Y?1Y@1YI1YJ1YK1YL1YQ1YT1Y^1ZD1ZW1Zj1[=1[P1[e1\81\^1\h1\n1]71]81]G1]V1]W1]b1]g1^61^71^81^91^:1^;1^<1^A1^G1^M1^U1^a1^i1^m1_11_21_31_41_51_61_?1_J1_P1_U1_ZS4CEIL2LO1H3HspS4CEIL2LO3CX1S4AHIaS4CEIL2LO1H3HspSS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S4AHIaSS3LSJ3TICSS2LOSSSSSS4CEIL2LO3CX13Hsp2T13LSJS4AHIaS3LSJ3TICS3NSR3MSB3CWF1YSS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S3SZ83SZP3SH11HS3SZ83SZP3SH11HSS2HBFFS4AHIaS4AHIaS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS4AHIaS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14FFSS3NSR3NSBFS3NSR4PA0b4PA0c3MSB3CWF3SH13SH22LTSS3LSJ3TICS3AALS3AAL2A0S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9SS2A0SSFFS4CEIL2LO3LSJ3MSB2A04AHId3SZP3SH54ASDa4ASDb3HspS4CEIL2LO3LSJ3MSB2A04AHId3SZP4ASDa4ASDb3HspS3LSJ3TICS3LSJS3LSJS3MSBS4AHIaS4AHIaSSFFSS4AHIaS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspSS3LSJS3CWFS3LSJ3TICS4AHIaS3AALS3HspFS4AHIaSSS4AHIaS4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23SH53HspS3LSJS4CEIL2LO1HS3LSJS3NSRS2LOS4AHIaS4AHId1HS4AHIaS2LOSS3MSBS3LSJ3TICS4CEIL2LO1HS4CEILS4CEILS4CEILS4CEILSS4AHIaS4AHIaS2HBS3MSB4AHIb4AHIc3SH13SH2FFS4CEIL2LO3LSJ3MSB2A01H3SZP3SH23HspS4AHIaS3LSJ3TICSFFSSS3SPRSS4AHIaS2T1FFFFFS4CEIL2LO2T1S4AHIaS4CEIL2LO3CX11HS4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0S4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0SSFFSS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3LSJS4AHIaSS3NSR3CWF2LT1YSS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdS4AHIaFS4CEIL2LO1HFSSS2HqS3LSJ3TICS3MSBS4CEIL2LO1HS3NSR4NRB0S3NSR3MSB3CWF1YS4CEIL2LO1H3HspS3HspS4CEIL2LO1H3HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO4PA0d3CWF2LTS4CEIL2LO1H3HspS2HBS4CEIL2LO1HS3LSJ3TICS4CEIL2LO1H3HspS3LSJ3TICS2HBS3HspS3LSJ3TICSS3LSJ3TICS4CEIL2LO3LSJ2NB3RSR3NSE3MSR3MSB2A01H3SZ83SZP3SH23SH53Hsp3CX13SH15CBNDa5CBNDb2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSB2A01H3SZP3SH23SH53HspS4CEIL2LO3CX13LSJ3MSB2A03SZP3SH13SH25CBNDa5CBNDb3Hsp1H2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23HspSSS4CEIL2LO4PA0d3CWFS4AHIaSSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS2HBS4AHIaSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS2LOS4AHIaS3NSR4PA0aSS3NSR4PA0aS2HBSSFFS3LSJS3CX1S4CEIL2LO1H3SH13HspS3SPRS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3MSBFSS4AHIaS3NSR3NSBS4AHIaS3SPRS3LSJ3TICS3LSJ3TICSSSS3LSJ3TICS4AHIaS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3NSRS3MSMS4CEIL2LO3MSB3SH21HS4CEIL2LO1HS4AHIaSSS2A0S3LSJ3TICSS3NSB1Y1ES4AHIaS2HBS3LSJ3TICS2HBS4AHIaS4AHIaSS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdSS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS4AHIaS3SPRFS3SZPS3NSR4NRB03NSBSSS3MSBS1N2NB3RSR3NSES3MSR3MSBS4CEIL2LO3MSB4AHIdS4AHIaSS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0S4AHIaS3AALS4AHIaS2HBS3MSR3MSB4ASDa4ASDb1H2H02H42H5S3MSR3MSB4ASDa4ASDb1H2H02H42H5S4CEIL2LO1HSSS4CEIL2LO4AHIdS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSS2LOSFFS3LSJ3TICS3MSBS3MSBS3AALS2A0S4AHIaS4CEIL2LO1HS3NSR4PA0aS4CEIL2LO2T1S1Y2Y0S4AHIaFS3AAL3SZ8S3MSB3AAL2A04AHIa3SZ83SZP3MSR1YSSSSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3NSR4PA0aSS3MSB2A04AHId1HS2A0S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S2LOSS3LSJ3TICS3LSJ3TICFS4AHIaS2LOS4AHIaS3MSBS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3HspS4AHIaS4CEIL2LO1HS4AHIaS4AHIaSSS4CEIL2LO3MSB4AHIdS3TICS3TICS3LSJSS3LSJ3TICS4AHIaS3LSJ3TICSFSS4CEIL2LO1HSSS4CEIL2LO1HSSS3SZPS4PA0d3CWF1HS2LOSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3HspSSSSS4CEIL2LO1H3HspS4AHIaS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFSSSSSS3TICS3MSB2A04AHId1HS3MSB2A03ACE1HS4CEIL2LO1HS4CEIL2LO3MSB4AHIdS4CEIL2LO3SPR1HS4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0S4AHIaS3MSB3SH13SH25TBNDa5TBNDbS3MSR3SZ81YSSS4AHIaFFS4CEIL2LO2AH1HSSS4AHIaS2LOS3SPRSS2T11HSS3NSR4PA0aS3NSR2KQS4PA0a3MSB4AHIa1YS4PA0a3MSB4AHIa1YS3SPRS3SPRS4AHIaS4AHIaS4AHIaS2LOS4AHIaSSSFFS3AALSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4AHIaS4AHIaS2HBSS4CEIL2LO1H3HspS3LSJ3TICS4CEIL2LO4PA0d3CWF2LTS4CEIL2LO4PA0d3CWF2LTS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YSS3NSR2KQS3MSRSS3NSR4PA0aS3NSR4PA0aS4CEIL2LO1HS3LSJ3MSB2A03SZP3SH5FS4CEIL2LO4PA0d3CWFS5TBNDa5TBNDbS3LSJ3TICS3MSB4AHIa4AHId1HS3MSB4AHIa4AHId1HS4AHIaSS3NSR3MSB2KQ3CWF1YS3NSR4PA0a3MSB3CWF2LT2Y0S4AHIaSS3NSR4PA0b4PA0c3MSR3MSB3CWF3SZ83SH13SH23SH52LT1Y2H42H9S3LSJ3TICS4AHIaS2LOSS3MSBS3MSBS3MSBS3MSBS3MSBS3MSR3MSB3SH13SH25TBNDa5TBNDb1H2H02H42H5S3NSR4NRB0S3NSR4NRB0S3NSR4NRB0S4AHIaS4CEIL2LO1H3HspS3LSJ3TICSS3CXIS4AHIaS3CXIS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS3MSB4AHIb4AHIc3SH13SH2S3MSB4AHIb4AHIc3SH13SH2S3MSB4AHId1HS4AHIaS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSSSS4AHIaSS3LSJ3TICSS3MSR3MSB3SZ83SH13SH25TBNDa5TBNDb1Y1H2H42H52H9S4AHIa1YS4AHIa1YS3SPRS3SPRSSS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S2HBS4AHIaS3MSBSS3SPRS4CEIL2LO1H3HspS2LOS4CEIL2LO1H3HspSSFS3SPRS4AHIaS4CEIL2LO1HSSSSS3MSBS3MSBS3MSBSS4AHIaS4AHIaS1N3RSRS4CEIL2LO1HS5TBNDa5TBNDbS3CX11HS3MSBS4CEIL2LO4PA0d3CWF2LTSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4AHIaS4AHIaSS3LSJ3TICS2LOS4AHIaFS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YFS3LSJ3TICSS4CEIL2LO3MSB4AHIdS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSSS4AHIaSS3HspS3HspS3HspSS3LSJ3TICS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS4AHIaS2HBS3NSR4PA0aS4CEIL2LO1HS3NSR4PA0aS3CWF2HqS2HqS3CWF2HqS2K02A03ACE3SZP1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS3MSR3MSB3SZ81YS3LSJ3TICSSS4CEIL2LO1HS4AHIaS4AHIaSS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0S3CWFS3NSB1YSS4CEIL2LO1H3HspS3MSR2K0S3MSB2K7S3SZP2K53MSR2K6S2A02K1S3LSJ3TICSSS1YFFS2T11HS3LSJ3TICS4AHIaS3LSJ3TICS3LSJ3TICFS3LSJ3TICS3HspSSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4AHIaS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspFFS2LOS3MSB4AHIa1YS2LOS2LOS3SH1S3SH1SS2LOS2LOSSSS4CEIL2LO1H3HspFFS2HBS4CEIL2LO1H3HspFFS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H9S3LSJ3TICS2LOS2T11HSSS2HBS4CEIL2LO1H3HspS3NSR4PA0aS4CEIL2LO3MSB4AHIdS4AHIaSS3LSJ3MSB2A03SZPFS4AHIaS3NSR4PA0a3CWF2LT1YS3NSR4PA0aSS4AHIaS3HspS4CEIL2LO1H3HspS4AHIaSS4NRB0S4CEIL2LO1HS1YS1N2NB3RSR3NSESS3SPRS4CEIL2LO1H3HspS1YS4CEIL2LO1H3HspSSSS3SH1S3SH1S4CEIL2LO1H3HspS4AHIaSSS4CEIL2LO1HFS4AHIaFS3LSJ3TICS4CEIL2LO1HSS3LSJ3TICS3NSR2KQ3CWFSS3NSR3NSBSSSS3NSR3NSBS4CEIL2LO1HFS3LSJ3TICFSSS3LSJS1YS3NSR2KQ1YS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HS3AAL4AHIa4AHId3SZ81YS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3NSR4PA0aS4AHIaS3LSJ3TICSS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YSS4CEIL2LO1HS3MSBS4CEIL2LO1H3HspSSSSSSS3SPRS4AHIaS4AHIaS3CWF2HqS3MSB3CWF2HqS3MSB2HqS2HqS2HqFFFFFS3LSJ3TICS4CEIL2LO1HS4AHIaS3SH5S3LSJ".
assert (MS4 : exists q, ms = 4096 * q) by (exists (ms / 4096); clear -MSM MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  clear RSE. box MSE. box RSM. box MSM. box NRM. box PAL. box CT2. box DPT. box DPC.
  (* [comment removed for export] *)
  iprefix.
  carve_frame 96%nat ST.
  do 12 step.                                                  (* [comment removed for export] *)
  assert (HWL : Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv)) \/ (0x9da30 <= fst iv /\ snd iv <= 0xa0240))
                       [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z)
    by (apply Forall_cons; [cbn; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (large_cells_frame ctx t PA m mm _ LC MU WM ltac:(exact CXI) HWL) as LC1 end.
  destruct LC1 as (RC & PC & GNM & NAME & TI & TK & T88 & TSD & CT & I64). unfold ATP88, ATSD in *.
  step. zstep. zstep. step. if_lit.                            (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096)) ltac:(rewrite land_align4096 by (clear -MSB MSR; lia); f_equal; unbox MSE; rewrite MSE; clear -MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0.
  setreg 18 (Z_to_bv 64 ms) ltac:(f_equal; clear; lia).
  step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 MSR MSB NSE RSR N. subst size. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
  eapply (mmapz_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ms lo) end.
  all: try lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
       | |- mem_inv _ _ => assumption
       | |- rmap_cells _ => exact RC
       | |- rng_aimg _ => exact RIMG
       | |- @eq word _ _ => reflexivity
       | |- _ mod 4096 = 0 => unboxed MSM
       | |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
       end.
  all: try (atop_facts; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO MSB; lia).
  { (* [comment removed for export] *)
    intros a HFR A0 ACE. destruct (FROK a HFR) as (AH & _). unfold ablk, KLS, AIMG_HI in *.  (* [comment removed for export] *) rewrite unsigned_lit by (clear -SPR CEIL LO; lia). clear -AH ACE CEIL LO SPR. lia. }
  { (* [comment removed for export] *)
    intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
  (* [comment removed for export] *)
  intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
  destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
  destruct (FROK a HFR) as (AHI & DAT & DAC & DAP & SH0). box DAT. box DAC. box DAP.
  pose proof AHI as AHI0. clear AHI. destruct (ablk_int _ _ AHI0) as (kA & AHI & AHIa & AHIb & AHIc & AHId).   (* [comment removed for export] *)
  rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
  (* [comment removed for export] *)
  destruct (Z_lt_le_dec nsec 1048576) as [NSB|NSB].
  2: { eapply UNR3; [exact HFR | clear -NSB NSR NRB0; lia | clear -NSB NSR NRB0; lia]. }
  (* [comment removed for export] *)
  set (CW := if nsec =? nres then 131072 else 0).
  assert (ECW : CW = (if nsec =? nres then 131072 else 0)) by reflexivity.
  assert (CWF : 0 <= CW <= 131072 /\ 8 * nres + CW <= 8388608).
  { rewrite ECW. ub NRM. destruct (Z.eqb_spec nsec nres) as [E|E]; clear -NSB NSR NRB0 Y E; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  clearbody CW. box ECW.
  atop_facts.
  assert (SZ8 : size mod 8 = 0) by (rewrite NSE; ub RSM; clear -Y; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (SZP : 0 < size) by (rewrite NSE; clear -RSR N; lia).
  assert (SHR : 0x800b6c00 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000 /\ shlen ms = ms / 8 /\ shlen 4096 = 512
                /\ shad (a + 4096 + size) = shad a + 512 + size / 8 /\ shlen (ms - 4096 - size) = ms / 8 - 512 - size / 8).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. ub MSM. clear -AHI AHIa AHIb AHIc AHId ACE MSB AAL SZ8 K0 Y. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct SHR as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). rewrite SH3 in RSCH.
  destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(clear -MSB; lia)) as (kS & ASD & ASDa & ASDb & _ & _).   (* [comment removed for export] *)
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb). destruct (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (MU02 : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp + -96); (a, a + ms)]%Z m0 m2)
    by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia).
  assert (MUA : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
  assert (WMA : wmono bsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear MU WM MU2.
  xport FR MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport I64 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport GNM MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport NAME MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport TI MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TK MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport T88 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TSD MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  xport CT MU02 WM2 ltac:(ub DAC; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 Y CXI; dlia).
  assert (PC2 : poison_cells m2).
  { eapply poison_cells_frame; [exact PC | exact MU02 | exact WM2 |]. unfold AIMG_HI.
    apply Forall_cons; [cbn; clear -SPR CEIL LO; lia|]. apply Forall_cons; [cbn; clear -AHI AHIa AHIb AHIc AHId; lia| apply Forall_nil]. }
  clear PC RC ST.
  unfold fill_at in SH0. xport SH0 MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE SH1 SH2 MSB; dlia).
  unbox STATS. xport STATS MUA WMA ltac:(ub DAT; rewrite LSJ; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE T0 T1 Y TIC; dlia).
  unbox INS. xport INS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox SRT. xport SRT MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JST. xport JST MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JBS. xport JBS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox MTX. xport MTX MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  unbox JGL. xport JGL MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
  assert (JSL2 : nsec < nres -> rw_cells bsegs m2 (PA + 8 * nsec) [CB 8 jslot]).
  { intros LT. specialize (JSL LT). xport JSL MUA WMA ltac:(ub DAP; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT Y; dlia). exact JSL. }
  clear JSL.
  (* [comment removed for export] *)
  change (rw_cells bsegs m2 (shad a) [CB (Z.to_nat (ms / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms / 8)))]) with (fill_at m2 (shad a) (ms / 8) 0) in SH0.
  destruct (fill_split m2 (shad a) 512 (ms / 8 - 512) 0 ltac:(replace (512 + (ms / 8 - 512)) with (ms / 8) by (clear; lia); exact SH0) ltac:(clear; lia) ltac:(clear -MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia))
    as [SHH SHR0].
  destruct (fill_split m2 (shad a + 512) (size / 8) (ms / 8 - 512 - size / 8) 0 ltac:(replace (size / 8 + (ms / 8 - 512 - size / 8)) with (ms / 8 - 512) by (clear; lia); exact SHR0)
              ltac:(clear -SZP; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia) ltac:(ub MSM; clear -MSB K0 SZ8 Y MSR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia))
    as [SHU SHT]. clear SHR0.
  clear SH0.
  (* [comment removed for export] *)
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
  apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RPA.
  iprefix.
  replace (ret_pc (Z_to_bv 64 219736)) with (Z_to_bv 64 219736 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1 A0 ACE. lia. }          (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite (Z.land_comm 4095 a); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; symmetry; exact AAL).
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. zstep. zstep. zstep. zstep.                           (* [comment removed for export] *)
  change ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0. change (Z.land 0 8) with 0.
  setreg 25 (Z_to_bv 64 (a + 4096)) ltac:(f_equal; clear; lia).
  zstep. zstep. zstep. zstep.                                  (* [comment removed for export] *)
  setreg 23 (Z_to_bv 64 (a + 4096 + size))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 SZP; lia);
          change (2^3) with 8; clear -AAL SZ8 A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  setreg 10 (Z_to_bv 64 (a + 4096))
    ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 MSB; lia);
          change (2^3) with 8; clear -AAL A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 4096) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  clear MU02.
  apply (munch_weaken _ [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                          (0x9da48, 0x9dca8); (t + 2800, t + 3168);
                          (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z) in MUA.
  2: { unfold sub_fp. cbn [outside]. clear. intros q Hq. tauto. }
  (* [comment removed for export] *)
  unfold fill_at in SHH, SHU, SHT.
  pose proof PC2 as PCx. destruct PCx as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof RC2 as RCx. destruct RCx as (Q1 & Q2 & Q3 & Q4 & Q5). clear PC2 RC2 Q3.
  Local Ltac pcells := unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption.
  (* [comment removed for export] *)
  assert (RSH1 : rng RNG' (shad a) 512) by (eapply rng_sub'; [exact RSCH|]; clear -MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad a, shad a + 512)]%Z m2) as MUS. pose proof (wmono_refl bsegs m2) as WMS.
  step. call_sp (poison_shadow_spec_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 4096 512 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHH
       | |- rng _ (shad _) _ => exact RSH1
       | |- rng_aimg _ => exact RIMG
       | |- shlen _ = _ => exact SH4
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear; lia | clear -MSB; lia]).
  all: try (atop_facts; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB SPR CEIL LO; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  lazymatch goal with M : munch _ m2 ?mm, W : wmono bsegs m2 _ |- _ =>
    assert (JSL3 : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 MSB; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  zstep. step. step.                                           (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 4096 - size)) ltac:(f_equal; clear; lia).
  assert (RSH2 : rng RNG' (shad (a + 4096 + size)) (ms / 8 - 512 - size / 8))
    by (rewrite SH5; eapply rng_sub'; [exact RSCH|]; ub MSM; clear -MSB MSR SZP SZ8 K0 Y; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  rewrite <- SH5 in SHT.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad (a + 4096 + size), shad (a + 4096 + size) + (ms / 8 - 512 - size / 8))]%Z mm) as MUS;
    pose proof (wmono_refl bsegs mm) as WMS end.
  step. call_sp (poison_shadow_spec0_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096 + size) (ms - 4096 - size) (ms / 8 - 512 - size / 8) 250 lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => pcells
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => exact SHT
       | |- rng _ (shad _) _ => exact RSH2
       | |- rng_aimg _ => exact RIMG
       | |- shlen _ = _ => exact SH6
       | |- rng _ _ _ => solve_rng
       end.
  all: try (eapply ablk_sub; [exact AHI0 | clear -SZP; lia | clear; lia]).   (* [comment removed for export] *)
  all: try (atop_facts; ub MSM; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB MSR SPR CEIL LO SZ8 SZP K0 Y; first [lia | OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono bsegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(ub MSM; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 SH5 MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96)]%Z mm) as MUS; pose proof (wmono_refl bsegs mm) as WMS end.
  pose proof CT as CT0. box CT0. box ZCH. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  step. call_sp (thread_stats_spec RNG' ctx t lo).   (* [comment removed for export] *)
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ _ _ => assumption
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ _ => solve_rng
       end.
  all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 SPR CXI TIC; lia).
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono bsegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT; dlia); exact JSL2);
    clear JSL2; rename JSL3 into JSL2;
    (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96); (t + 2872, t + 2888)]%Z) in M;
    [ rename M into MUS2; rename W into WMS2 | unfold sub_fp; cbn [outside]; clear; intros q Hq; tauto ] end.
  clear CT.
  (* [comment removed for export] *)
  snapshot [(t + 2872, t + 2888); (a, a + 32); (0x9dc80, 0x9dc84)]%Z MUz WMz.
  aload STATS 9 (t + 2800 + 72).                               (* [comment removed for export] *)
  aload STATS 10 (t + 2800 + 80).                              (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 9.                                              (* [comment removed for export] *)
  astore STATS 10.                                             (* [comment removed for export] *)
  carry ZCH MUS2 WMS2 ltac:(ub DAT; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB T1 TIC; dlia).
  carry POST MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 T1 TBND TBNDa TBNDb; dlia).   (* [comment removed for export] *)
  carry SHU MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  carry POST0 MUS2 WMS2 ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP SZ8 K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
  clear MUS2 WMS2.
  step. if_lit.                                                (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 0) ltac:(f_equal; try rewrite (Z.land_comm 4095); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; clear -AAL A0; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. if_lit.                                                (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. clear -K5 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  step. if_cases K6; zify_cond K6. { exfalso. clear -K6 A0 SZP ACE MSR. lia. }       (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 21 (Z_to_bv 64 a) ltac:(f_equal; clear; lia).
  (* [comment removed for export] *)
  lazymatch type of ZCH with rw_cells _ ?mq _ _ =>
    change (fill_at mq a ms 0) in ZCH;
    destruct (fill_split mq a 32 (ms - 32) 0 ltac:(replace (32 + (ms - 32)) with ms by (clear; lia); exact ZCH) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZH ZR];
    destruct (fill_split mq (a + 32) (4096 - 32) (ms - 4096) 0 ltac:(replace (4096 - 32 + (ms - 4096)) with (ms - 32) by (clear; lia); exact ZR) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZP ZU]
  end.
  clear ZCH ZR. apply zeros32_hdr in ZH. unfold fill_at in ZP, ZU. replace (a + 32 + (4096 - 32)) with (a + 4096) in ZU by (clear; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells bsegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 MUz WMz ltac:(ub DPT; ub DAP; clear -Y Y0 SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT T1 AHI AHIa AHIb AHIc AHId ACE MSB TIC; dlia); exact JSL2);
    clear JSL2 MUz WMz; rename JSL3 into JSL2 end.
  box STATS. box ZP. box ZU. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + 32); (0x9da48, 0x9dca8);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z MUr WMr.
  snapshot [(a, a + 32); (0x9dc80, 0x9dc84)]%Z MUq WMq.      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. if_cases K7; zify_cond K7. { exfalso. clear -K7 MSB. lia. }                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 646272) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. step. if_lit.                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by (clear; lia); clear -NSR NSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (slog_facts ms MSB ltac:(ub MSM; exact Y)) as [CSR CLZ].
  do 25 zstep. setreg 11 (Z_to_bv 64 (cb_sm ms)) ltac:(reflexivity).              (* [comment removed for export] *)
  do 7 zstep. step. do 9 zstep.                                (* [comment removed for export] *)
  setreg 19 (Z_to_bv 64 (cb_clz (cb_sm ms))) ltac:(reflexivity).
  step. if_cases KQ; zify_cond KQ.
  - (* [comment removed for export] *)
    clear MUq WMq JSL2. subst nsec.
    assert (NRB : nres + 16384 <= 1048576) by (ub NRM; clear -NSB Y NSR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    assert (ECW1 : CW = 131072) by (ub ECW; rewrite Z.eqb_refl in Y; exact Y).
    clear CWF. assert (CWF : CW = 131072 /\ nres + 16384 <= 1048576) by (split; [exact ECW1| exact NRB]).
    step.                                                      (* [comment removed for export] *)
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (PA + 8 * nres)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NSR; lia).
    step. step. step. step.                                    (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    apply evtF_done. rewrite (SHAPE2 a HFR eq_refl NRB).
    lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (rmapd_spec RNG' (K2 a) Q _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (PA + 8 * nres) 131072 lo) end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eassumption
         | |- mem_inv _ _ => assumption
         | |- rmap_cells _ => unfold rmap_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption
         | |- rng_aimg _ => exact RIMG
         | |- @eq word _ _ => reflexivity
         | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
         | |- (_ + 8 * _) mod 4096 = 0 => ub NRM; ub PAL; clear -Y Y0 NSR; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
         end.
    all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF; lia).
    { (* [comment removed for export] *) intros r RNG'' ms' NE R0 RCE. eapply UNR2; [exact NE | exact R0 | exact RCE]. }
    (* [comment removed for export] *)
    intros RNG'' mc q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 PM.
    destruct PM as (FPLE2 & PCE & MUc & WMc & MIc & STc & ZC & RPC & RSPC & BW2 & RCc).
    rewrite unsigned_lit in MUc, STc by (clear -SPR CEIL LO; lia).
    (* [comment removed for export] *)
    xport FR MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport I64 MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport INS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport SRT MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JST MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JBS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport MTX MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    xport JGL MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
    (* [comment removed for export] *)
    xport ZH MUc WMc ltac:(ub DAP; clear -Y SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB; dlia).
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr2 : munch Wr ma mc) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr2 : wmono bsegs ma mc) by (eapply wmono_trans; [exact WMr | exact WMc]) end.
    clear MUr WMr. rename MUr2 into MUr. rename WMr2 into WMr.
    lazymatch type of MUA with munch ?Wa ?ma ?mb =>
      assert (MUA2 : munch Wa ma mc) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMA2 : wmono bsegs ma mc) by (eapply wmono_trans; [exact WMA | exact WMc]) end.
    clear MUA WMA MUc WMc. rename MUA2 into MUA. rename WMA2 into WMA.
    apply (rng_fp_le _ _ _ _ FPLE2) in RIMG. apply (rng_fp_le _ _ _ _ FPLE2) in RSTK. apply (rng_fp_le _ _ _ _ FPLE2) in RCH.
    apply (rng_fp_le _ _ _ _ FPLE2) in RSCH. apply (rng_fp_le _ _ _ _ FPLE2) in RPA.
    iprefix.
    replace (ret_pc (Z_to_bv 64 220664)) with (Z_to_bv 64 220664 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
    step.                                                      (* [comment removed for export] *)
    step. step.                                                (* [comment removed for export] *)
    step. zstep.                                               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch type of ZC with rw_cells _ ?mq _ _ =>
      change (fill_at mq (PA + 8 * nres) 131072 0) in ZC;
      destruct (fill_split mq (PA + 8 * nres) 8 (131072 - 8) 0 ZC ltac:(clear; lia) ltac:(clear; lia)) as [ZC8 ZCR] end.
    clear ZC. unfold fill_at in ZC8, ZCR.
    assert (RPS : rng RNG'' (PA + 8 * nres) 8) by (eapply rng_sub'; [exact RPC|]; clear; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG'' (bv_unsigned sp)); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      all: try reflexivity.
      all: try (ub DAP; atop_facts; clear -Y CEIL LO SPR NSR NRB0 CWF PCE; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    destruct PT as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & ZH9 & INS9 & SRT9 & JST9 & JBS9 & MTX9 & JGL9 & PAS9).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono bsegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    xport ZCR MU9 WM9 ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0x9da48, 0x9dca8); (t + 2800, t + 3168);
                         (PA + 8 * nres, PA + 8 * nres + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono bsegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT2 a RNG'' m9); [exact HFR | reflexivity |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [eapply fp_le_trans; [exact FPLE| exact FPLE2]|]. split; [exact BW2|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app bsegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nres)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [right; split; [reflexivity|]; split; [reflexivity|]; split; [exact ZCR| exact RPC]|].
    split; [clear -CWF; lia|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  - (* [comment removed for export] *)
    assert (ECW0 : CW = 0) by (ub ECW; destruct (Z.eqb_spec nsec nres) as [E|E]; [exfalso; exact (KQ E) | exact Y]).
    clear CWF. assert (CWF : CW = 0 /\ nres <= 1048576) by (split; [exact ECW0| exact NRB0]).
    specialize (JSL2 ltac:(clear -KQ NSR; lia)).
    xport JSL2 MUq WMq ltac:(ub DAP; clear -Y SPR CEIL LO NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1 AHI AHIa AHIb AHIc AHId ACE MSB KQ; dlia). clear MUq WMq.
    assert (RPS : rng RNG' (PA + 8 * nsec) 8) by (eapply rng_sub'; [exact RPA|]; clear -KQ NSR; lia).
    eapply evtF_cut.
    { eapply (large_tail_spec RNG' (bv_unsigned sp)); try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast.
      all: try reflexivity.
      all: try (ub DAP; clear -Y CEIL LO SPR NSR NRB0 CWF KQ; lia). }
    cbv beta. intros ms9 PT. unfold large_tail_post in PT.
    destruct PT as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & ZH9 & INS9 & SRT9 & JST9 & JBS9 & MTX9 & JGL9 & PAS9).
    apply evtF_done. rewrite Z_to_bv_bv_unsigned.
    (* [comment removed for export] *)
    lazymatch type of MUr with munch ?Wr ?ma ?mb =>
      assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMr9 : wmono bsegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0x9da48, 0x9dca8); (t + 2800, t + 3168);
                         (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono bsegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT1 a RNG' m9); [exact HFR | exact KQ |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app bsegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)] [CB _ _])).
             split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
    split; [exact ZU|].
    split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
    split; [exact RCH|]. split; [exact RSCH|].
    split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
    split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
    split; [exact PAS9|].
    split; [left; split; [exact KQ| reflexivity]|].
    split; [exact NRB0|].
    eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
    ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.   (* [comment removed for export] *)
    repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
