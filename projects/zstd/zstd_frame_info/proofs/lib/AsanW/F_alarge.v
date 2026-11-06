(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import MM_syscalls StrFun.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ABytes AKit AKit2 AKitQ AModelFacts APrimFacts ASecFacts ASecSlog RT_stubs ARep ARepKit
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
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition large_entry := 0x35998.
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
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=24437255187.643957821123.600000900?S1H2H02G2S1H2H0".
destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
  /\ rw_cells asegs m 0x98e20 [C8 (Z_to_bv 64 0x9acf8)] /\ rw_cells asegs m 0x9acf8 [C8 (Z_to_bv 64 0x191d0)]
  /\ rw_cells asegs m 0xa06e0 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xa06e4 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)]
  /\ rw_cells asegs m 0x9d858 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)].      (* [comment removed for export] *)

#[using="Type"] Lemma large_cells_frame : forall ctx t PA m m' W, large_cells ctx t PA m -> munch W m m' -> wmono asegs m m' ->
  AIMG_HI <= ctx ->
  Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv))      (* [comment removed for export] *)
                    \/ (0x9d870 <= fst iv /\ snd iv <= 0xa0080)) W -> large_cells ctx t PA m'.
Proof.
  intros ctx t PA m m' W LC MU WM CX HW.
  destruct LC as ((Q1 & Q2 & Q3 & Q4 & Q5) & (P1 & P2 & P3 & P4 & P5 & P6 & P7) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  unfold AIMG_HI, AIMG_LO, ATP88, ATSD in *.
  assert (D : forall A k, 0 <= k -> ((0x10000 <= A /\ A + k <= 0x9d870) \/ (0xa0080 <= A /\ A + k <= 0x5f6000) \/ (A = ctx + 152 /\ k = 8)) -> disjoint_from W A k).
  { clear -HW CX. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold large_cells, rmap_cells, poison_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | unfold ATP88, ATSD; cbn; apply D; lia]).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeros32_hdr : forall m A, fill_at m A 32 0 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0x9dac0 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x9dac0 [C4 (Z_to_bv 64 b)].
Proof.
  intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
  cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=38834543651.557022093363.560302399878.5000004005006S2HbSS".
replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
  rw_cells asegs m 0x9dac0 [C4 (Z_to_bv 64 b)] ->
  rw_cells asegs m 0x9dac0 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
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
  /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
                          CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))]
  /\ rw_cells asegs m' res [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))]
  /\ fill_at m' (shad a) 512 0xfa
  /\ fill_at m' (shad a + 512) (size / 8) 0
  /\ fill_at m' (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa
  /\ rng RNG' a ms /\ rng RNG' (shad a) (ms / 8)
     (* [comment removed for export] *)
  /\ rw_cells asegs m' 0x9d888 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
  /\ rw_cells asegs m' 0x9d898 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0x9d8a0 32 /\ junk_at m' 0x9d8c0 512
  /\ rw_cells asegs m' 0x9dac0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0x9dad8 16
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)]
  /\ ((nsec <> nres /\ nres' = nres)
      \/ (nsec = nres /\ nres' = nres + 16384
          /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]
          /\ rng RNG' (PA + 8 * nres) 131072))
  /\ nres' <= 1048576
  /\ large_cells ctx t PA m'.

(* [comment removed for export] *)
#[using="Type"] Lemma c8x4_of_junk : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  destruct (c8c8_of_junk m A J1) as (w1 & w2 & H1). destruct (c8c8_of_junk m (A + 16) J2) as (w3 & w4 & H2).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
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
             F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ munch [(sp0 - 96, sp0); (a + 24, a + 32); (0x9d888, 0x9dae8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp0
    /\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)]
    /\ rw_cells asegs m' 0x9d888 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
    /\ rw_cells asegs m' 0x9d898 [C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0x9d8a0 32 /\ junk_at m' 0x9d8c0 512
    /\ rw_cells asegs m' 0x9dac0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ junk_at m' 0x9dad8 16
    /\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].

#[using="Type"] Lemma large_tail_spec : forall RNG (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a ms size PA nres' nsec k lo : Z) (srt : byte) (fj jstats jbsl jglob jslot : list byte),
  stk asegs m lo (sp0 - 96) -> ATOP <= lo -> lo <= sp0 - 96 -> sp0 < 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (sp0 + -96) [CB 8 fj; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells asegs m 0x9d858 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x9d888 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0x9d898 [C1 srt] ->
  rw_cells asegs m 0x9d8a0 [CB 32 jstats] -> rw_cells asegs m 0x9d8c0 [CB 512 jbsl] ->
  rw_cells asegs m 0x9dac0 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0x9dad8 [CB 16 jglob] ->
  rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot] ->
  ablk a (a + ms) -> a + ms <= ATOP -> (a + ms <= PA \/ PA + 8388608 <= a) ->
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> 0 <= nsec -> 8 * nsec + 8 <= 8388608 -> 0 <= nres' < 2^64 ->
  73728 <= ms <= 536821760 -> 34 <= k <= 47 ->
  rng_aimg RNG -> rng RNG lo (sp0 - lo) -> rng RNG a ms -> rng RNG (PA + 8 * nsec) 8 ->
  evtF asegs RNG (large_tail_post sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 F fc a ms size PA nres' nsec lo fj m)
    (MS (mkR ra (Z_to_bv 64 (sp0 + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0x9dac8) (Z_to_bv 64 0x9d858) a0 a1 a2 (Z_to_bv 64 nsec) a4 a5 a6 a7
             (Z_to_bv 64 ms) (Z_to_bv 64 k) s4 (Z_to_bv 64 a) s6 s7 s8 s9 s10v s11v t3 t4 t5 t6)
        F (Z_to_bv 64 0x35bfc) fc None m (seg_rom asegs)).
Proof.
  intros until jslot. intros ST CEIL LO SP64 MI FR I64 ZH INS SRT JST JBS MTX JGL JSL AHI ACE DAP PA0 PA1 NS0 NS1 NR MSB KB RIMG RSTK RCH RPS.
  pose proof AHI as AHI0. pose proof PA0 as PA00. clear AHI PA0. destruct (ablk_int _ _ AHI0) as (kA & AHI & AHIa & AHIb & AHIc & AHId). destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).   (* [comment removed for export] *)
  atop_facts.
  pose proof (munch_refl [(sp0 - 96, sp0); (a + 24, a + 32); (0x9d888, 0x9dae8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  box DAP.
  destruct (c8_of_junk m (PA + 8 * nsec) (ex_intro _ jslot JSL)) as [wj PAS]. clear JSL.
  step.                                                        (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0360?10350723376.11810507237851.12110862073820.11811364738669.1121155308877.120 11799361125.11212053063107.2  12121701742.2  12300957722.12012568647620.12912589007235.12012912894256.11813168802263.16 13219909487.11713584623497.11713890452656.12914070288003.12014077038708.12114507198897.12715151186337.0  15234102944.11715342322172.12415342322175.12515675919530.1  15978027795.11816823685680.12117768877444.12918293628292.12918459507890.10618661153180.1231869417598.0   19137453636.11719438934449.12719554994992.12219868549745.11920394681972.12120915638832.12121423182316.12721723925508.11721740645168.12222108918349.11922823585411.12022829503024.12122975014380.12723052457452.12723077509607.12624460701407.12125024748988.11825866612400.12927039972100.11727050862559.11427445073329.12527975202284.12728193661232.12228768091006.12629282142829.11229372295851.1  30383459465.12031000663539.12331153249960.1  31338359551.12231790753535.12531971821036.12732009951492.11732356565379.120328053492.121  33100000457.12333267416045.12833323592496.11833803313712.12134176476781.1173418254762.127 34337641204.12134509919194.10835305913430.2  36246032048.12936515323085.12737032491140.12937625410381.12137959139888.12138056291523.12438887058579.1293894609928.111 39005674622.12639171077876.12139188636933.0  39332637397.0  39453804551.11239453804551.11739453804551.11839453804551.12039453804551.12139453804551.12239453804551.12739453804551.12939523907516.12239777698592.12939816364432.12139863266925.11239934446001.12640489262708.12140773122600.12740908647812.12941138286099.12141545695612.12441561305689.1164189464191.125 41895735382.11042061375533.12342532481613.1164274807917.120 42974364865.12443088781403.12143142798140.12943355002723.1  4377449905.126 44652134833.12644973528685.11245152091657.12045305250815.12945964270975.12546194827934.11246856997892.11746983758296.11847066581131.1294726867587.120 47856399731.11748773843565.1125010566057.117 506472808.129  51449059823.1295152994737.125 51542129412.1175201121389.112 52075430765.12152078938469.1  52350443184.12952637527600.12153287003779.12053556182192.12953761380468.12154560324002.11654568455164.12454693945639.12754759028852.12155086134004.12155263691249.11955349214303.12155356975804.12155618160944.11855664284081.12656008580081.12756156277492.12156180210559.1295627157937.125 5627157937.126 56747988284.12057529370628.1175766123124.121 57941532683.12958049312993.4  5805604584.118 58186409136.12958356055668.12158664418024.12259651704336.12159796477325.2  60774132814.2  61588179377.12562453639984.12262454476932.12962546880113.11562995630236.16 6314119924.121 63285576040.12563845449177.12863871191344.11863978504684.12764639615363.12064806989052.12465032630433.0  65447523820.1276570819460.129 66124323454.12666861428735.12566989559971.12767475915206.11367476546687.12267924011312.12268099503860.12168157851057.1277276411184.122 7826287891.122 8188422960.118 8490749549.112 8901311464.121 8965918046.119 9583930681.1   00000100:00>00D00E00F00J00N00O00U00c00d01301>01?01@01N01O01P01Q01[01_01c01d01o02002102202602702802>02?02@02A02B02C02L02M02Q02R02`02a02j03303703B03L03M03N03O03P03Y03Z03^03d03e03f03o04004904=04F04G04U04V04W04X04Y04Z04[04i04m05205605705805<05@05A05B05M05Q05U05V05W05X05Y05Z05[05\05]05^06?06@06J06T06^06d06e06k07=07>07I07M07N07R07X07Y07Z07[07\07e07o08008108208808908B08F08X08Y08]08f09409509;09<09B09M09N09O09U09V09W09X09Y09g09h09i09j09n0:A0:B0:C0:D0:O0:Y0:Z0:[0:\0:]0:f0:g0:h0;>0;?0;@0;I0;J0;P0;Q0;R0;X0;b0;f0;g0;h0;i0;j0;k0<:0<;0<?0<@0<A0<J0<X0<\0<]0<f0<g0<k0<o0=00=90=B0=C0=I0=J0=K0=V0=W0=]0=c0=g0=hSS2KB4HBSBS2LOS4AHIaSSS2KBS2KBSS4AHIaS3NS03HPS4PA0aSS3NS03NS13MSB1YS4CEIL2LO1HSSS3NS03HPS4PA0aSSSS3NS04PA0aS2LOS2LOSS4CEIL2LO1HSSSS2KBFSS4AHIaSSSSSS2KB4HBSBSS2KBSS3NS03HPS4PA0aSS2KB4HBSBS2KB4HBSBS2HBS4CEIL2LO1HS3NS04PA0aSSFSS2KB4HBSBSS2LOS4AHIaSSS2KB4HBSBSS2KB4HBSBS2LOS2KB4HBSBSS3NS03HPS4PA0aSFSSSSS2KB4AHIa4HBSBS2KBS3MSBS2KBSSS2KBS2KBSSS4CEIL2LO1HS2HBS2LOSSSSSSSSSS4CEIL2LO3NS02KB4AHIa4PA0a1H4HBSBSS3NS04PA0aS3NS04PA0aS3NS04PA0aS4AHIaSS4AHIaS3NS02KB4PA0a4HBSBSS4CEIL2LO1HS2LOSS2LOS4AHIaFSSSS2KB4HBSBS3NS04PA0aSSSS4AHIaSS2KB4HBSBS2LOS4CEIL2LO3MSB4AHIdSS2HBS2KB4HBSBS3NS03HPS4PA0aSS4AHIaSS4AHIaS4CEIL2LO1HSSS4AHIaSSSSS3NS03HPS4PA0aSSSS2LOS4CEIL2LO2KB1H4HBSBSSSS4CEIL2LO1HS3NS04PA0aSSSSS2KB4HBSBSSS4CEIL2LO3NS13HPS4PA0dSSS2KB4HBSBSS4AHIaSSS4AHIaS3NS04PA0aS2KBSSSSSS3NS03NS13MSB1YSS2HBSSS2KB4HBSBS3NS03HPS4PA0aS2LOSS2KB4HBSBSS2LOS2LOSS3NS03NS1S2KB4HBSBSS4AHIaSSS4CEIL2LO1HSS4AHIaS4AHIaS2HBS".
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
  destruct (c8x4_of_junk _ 0x9d8a0 (ex_intro _ jstats JST)) as (w1 & w2 & w3 & w4 & AST). clear JST.
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (junk_split _ 0x9d8c0 (8 * (63 - k)) (512 - 8 * (63 - k)) ltac:(replace (8 * (63 - k) + (512 - 8 * (63 - k))) with 512 by (clear; lia); exists jbsl; exact JBS)
              ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as [JB1 JB2].
  destruct (junk_split _ (0x9d8c0 + 8 * (63 - k)) 8 (512 - 8 * (63 - k) - 8) ltac:(replace (8 + (512 - 8 * (63 - k) - 8)) with (512 - 8 * (63 - k)) by (clear; lia); exact JB2)
              ltac:(clear; lia) ltac:(clear -KB; lia)) as [JBW JB3]. clear JB2 JBS.
  destruct (c8_of_junk _ _ JBW) as [wb BSL]. clear JBW. destruct JB1 as [bs1 JB1]. destruct JB3 as [bs3 JB3].
  remember (0x9d858 + 8 * (63 - k)) as BSB eqn:HBSB.
  replace (0x9d8c0 + 8 * (63 - k)) with (BSB + 104) in BSL by (subst BSB; clear; lia).
  replace (0x9d8c0 + 8 * (63 - k) + 8) with (BSB + 112) in JB3 by (subst BSB; clear; lia).
  step. if_cases KM; zify_cond KM.
  all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x35c40) _ _ _ _) => step end.   (* [comment removed for export] *)
  all: zstep; zstep.                                           (* [comment removed for export] *)
  all: setreg 11 (Z_to_bv 64 BSB) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); subst BSB; clear -KB; lia).
  all: step.                                                   (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: step; step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: destruct (c8c8_of_junk _ 0x9dad8 (ex_intro _ jglob JGL)) as (g0 & g1 & GL); clear JGL.
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0x9dad8) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: zstep.                                                  (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0x9dae0) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: apply (mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: do 13 step.                                             (* [comment removed for export] *)
  all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -96) (CB 8 _ :: _) |- _ => lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  all: apply evtF_done; unfold large_tail_post; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact ZH|]. all: split; [assumption|]. all: split; [assumption|].
  all: split; [exact (junk_of_cells _ _ _ AST)|].
  all: split.
  1,3: subst BSB; replace 512 with (8 * (63 - k) + (512 - 8 * (63 - k))) by (clear; lia);
       apply junk_merge; [exists bs1; exact JB1 | | clear -KB; lia| clear -KB; lia];
       replace (512 - 8 * (63 - k)) with (8 + (512 - 8 * (63 - k) - 8)) by (clear; lia);
       apply junk_merge; [ | | clear; lia | clear -KB; lia];
       [ replace (645312 + 8 * (63 - k)) with (645208 + 8 * (63 - k) + 104) by (clear; lia); exact (junk_of_cells _ _ _ BSL)
       | replace (645312 + 8 * (63 - k) + 8) with (645208 + 8 * (63 - k) + 112) by (clear; lia); exists bs3; exact JB3 ].
  all: split; [assumption|]. all: split; [| assumption].
  all: exact (junk_of_cells _ _ _ GL).
  Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma large_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
    (Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
  let size := needed_size n in let ms := sec_map_size n in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0x9d858 -> a1 = Z_to_bv 64 0x9dac8 ->      (* [comment removed for export] *) a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  large_cells ctx t PA m ->
  (* [comment removed for export] *)
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x9d888 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0x9d898 [C1 (Z_to_bv 8 sorted)] ->
  rw_cells asegs m 0x9d8a0 [CB 32 jstats] ->
  rw_cells asegs m 0x9d8c0 [CB 512 jbsl] ->
  rw_cells asegs m 0x9dac0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0x9dad8 [CB 16 jglob] ->
  (* [comment removed for export] *)
  ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->      (* [comment removed for export] *)
  0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
  (nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
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
      implS asegs RNG' (K a) (epostF Q) ms') ->
  (* [comment removed for export] *)
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
      implS asegs RNG' (K a) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (* [comment removed for export] *)
  (forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
      K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
  (* [comment removed for export] *)
  (forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
  (forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
  (forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
      implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Proof.
  intros until jslot. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
         PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.   (* [comment removed for export] *)
  pose proof PA0 as PA00. clear PA0. destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).   (* [comment removed for export] *)
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  unfold AIMG_HI, AREQMAX, large_entry in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  set (size := needed_size n) in *. set (ms := sec_map_size n) in *.
  (* [comment removed for export] *)
  box STATS. box INS. box SRT. box JST. box JBS. box MTX. box JGL.
  (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "0;_0?10020140617.25710026074842.25210145486483.22 10497310810.25210864281461.64 10864281461.65 10940398829.26610942156672.17 1149840136.0   11499002610.24711566666413.4  1162083375.125 11774978335.26411799361125.12711799361125.12811799361125.12911799361125.13011799489570.25211805889266.24711991125079.32 12178473528.54 12322440645.4  12358518976.12812428150072.23112430247196.24812542233325.2661256076226.17  12567643373.26612604608705.2671261375960.212 1261375960.260 1261375960.261 1261375962.257 12870277089.64 12870277089.65 13049158068.25813159172246.5  13313577562.3  13503541744.35 13685992690.24713700146930.2471370718544.2   1374799060.20  13892155040.45 13918739985.20 14040914212.25814043218912.24714085076929.26714153788013.2681450162113.267 14618011854.24814620109034.23114642883314.24714697527355.52 14697527355.53 14832399085.26615041073143.24615041134720.24715041903002.10 15176039361.2671538918798.32  1602526669.33  16148322415.24616189233663.18 16305613042.24716460365696.17 16599186802.24816682794945.26716709567841.3  16804761832.3  16831639642.3  17151130279.12717210349934.2  17318890361.55 17318890361.56 17511488259.24917538010112.24817542202648.24717559379343.18 17594417445.15 1765098690.17  17730919860.2581773310350.26  17738830189.32 17776320431.12517807136772.24617830068084.2931785468898.3   17986879152.10 17986879152.15 17986879152.20 17986879152.26 17995455655.12618361259584.12718422146077.20 18548796306.23218802973426.24718893283577.33 18913870613.6  18918200149.24718930958230.20 19030237063.24819032334243.23119042827563.12819092398759.12619338924274.2471937063194.15  19617313304.11 19617313304.15 19617313304.24 19617313304.27 19617313304.35 19658117869.26619670594045.24719836395674.25219885335399.10 19885335399.52 19885335399.53 19970277031.12620163737475.12520269398461.55 20269398461.56 20351462130.2472047665247.64  2047665247.65  2050035067.260 20519532770.52 20519532770.53 21055697588.25821127149840.29321171634930.24721227682692.33 2124193155.126 21284799705.25 21284799705.26 21362561773.26621405716698.25221468911858.24721472669832.8  21739104493.2662189954290.247 21900826496.17 22290347171.23222292444295.24922549005959.24822551103139.23122591943021.26822664701128.4  22706555394.6  2295126554.4   23101126068.25823173216193.37 23173216193.38 23386168314.18 23627005501.32 23726270554.25223770140939.3  2400638038.22  24147499556.26624189958221.17 24380253120.12524436996044.3  24694241473.26724880865951.2  24914674497.26725073974703.24825073974703.24925076071819.23125076071819.23225080282415.24725080282415.24825081078602.32 25245074452.47 25249020329.46 2546492594.268 25523975092.25825535372424.26525557086848.17 25638461890.33 25728983789.26625878270254.12626486114056.26726502771472.24726502771472.24826535314975.52 26535314975.53 26538147693.26826685873759.24626730776422.15 2673351043.52  2673627152.51  27147338155.12727199307648.17 27462345696.26327500699841.26727529010114.33 27574660128.25227776532267.2  27930427264.17 28028798645.4  28072922155.12928114192114.24728370640551.12528378782741.37 28378782741.38 28450832218.2  28628635885.26629067115679.19 29293392732.4  29364828409.33 2937190991.27  29406937538.33 29784318686.2  29875836246.26630008181843.10 30078181876.7  30414451008.12730521169266.248305622464.128  3059552449.267 30665193763.23230667290887.2493070846322.248 30805812953.25 30805812953.26 30884852660.25831012612437.0  31026020490.37 31026020490.38 31161366443.12831191324469.4  3137110253.266 31425461746.24731613213566.3  31649644204.5  31690874548.25831853783632.24831865172116.26131872282082.3  31881016690.24831929422313.14031936348496.5  32005092028.22 32088652577.0  32127996803.12632180001228.34 32180001228.38 32310233831.37 32310233831.38 3241391265.0   3263951075.3   32845911538.24732907263168.12732938500103.55 32938500103.56 33061971905.26733062543571.20 33062543571.26 33483765987.23133485863111.24833623804571.17 33739852525.26633764744995.23133766842119.24833793008176.4  33803036784.6  33890036527.12534164772537.6  34169364217.24734326450181.3  34330730127.10 34354335075.3  34374882658.26534398147309.26634413536621.26834539377394.2473457088893.248 34690630551.5  34862089154.33 34885248674.26834969462058.52 34969462058.53 35051326972.6  35115460349.26 35161916354.33 35205357699.12635209714819.12635340120754.26635435756793.33 35505011335.24835507108515.23135637039136.21235727064154.25235876479702.26435897425114.25235998161932.22 35998161932.37 35998161932.38 36115622446.12636180999398.11736266731970.17 36379156110.7  36442822002.24836459314100.25836475596894.55 36475596894.56 36651720741.20 36718281012.25836757669945.3  36807236845.26636976571392.17 3701516415.52  3701516415.53  37139260852.25837471900397.2663795062108.2   37973596975.2583799266425.1   38017335060.2663804798932.259 3804798932.260 38217320306.2483832836837.11  384436161.267  38692635477.0  38903098019.23238905195143.24938965490467.1  39012636437.0  39132412852.25839185847284.29339188636933.0  39332637397.0  39369634865.24839378986105.26439395200249.33 39661661252.4  39938181921.0  40084807026.20 40091925676.12440150930599.12640464152562.24740487747200.17 40556850541.26840583693037.26640600263088.3  4068729793.267 40823740273.29140832288750.26840834385893.26740834385896.26441270082071.37 41270082071.38 41272171651.12741408184389.26741408184390.26641408184392.26441410281550.26841476191879.2  41519412978.24741526574044.20641536595426.10 4172738.17     41779239794.24841797122996.25841844056301.26641844434310.64 41844434310.65 41880018802.24842006909334.22842132986300.32 42142204807.24842144301987.23142152594157.26642248457998.7  42250564277.21342250564277.23042250564277.24742263341421.2684237141073.27  42501170177.8  4259745615.25  4259745615.26  42803642915.24842805740039.23142887904618.12 429452623.25   429452623.26   4294687449.44  42979017140.25843061792653.11543121191467.12943308111674.3  43358680699.4  4339538087.127 43457716077.26843467924127.4  43497858498.17 43624396838.37 43624396838.38 43742893063.24843744990243.23143786047718.18 43786047718.19 43831372141.26843885339585.26743910045123.52 43910045123.53 43967845101.26643987951406.12644002291905.26744007240616.26444009337774.268440101998.1    44188571378.24744487020397.25244572497956.5  44582905172.3  44611301484.3  44663005684.29344698109568.17 4471461639.248 4473558819.231 44960421824.1274505138541.268 45172191085.26845378730119.24945380827299.23245456000882.24845486878294.35 45491065834.63 45607936882.24845656729165.25 45656729165.26 45980917854.5  45999893869.26846039653997.26846084819894.26 46219515605.1  46481087529.24746485146729.6  46932921792.33 46953039917.24747002471715.23147002471715.23247004568839.24847004568839.24947077647284.25847077701064.24747085737157.2344721740417.34  4721740417.38  47396727732.25847553697152.17 47757101492.25847895486285.17 48197302343.24948199399523.23248321848473.63 48506519986.24548688118565.10 48721597440.26448721597453.26748723694598.26848729649807.25348729650694.13048801560500.25848816565613.26848833333210.25248956220434.45 49081353231.26349082866238.19 49089206181.25749111512429.26849122645746.2474923662446.6   49421114917.2  49422484845.26849425192486.15 49486495821.25 49486495821.26 49608071770.25249669356060.37 49669356060.38 49819069809.20 49869996402.24849967586162.24850048241280.17 50079308762.25250092033716.25850108362994.24750131542183.12550189134306.7  50330077073.20 50516153480.0  50586667242.54 50600290453.52 50600290453.53 50610820429.17 50664164139.12950667712365.2685072571819.128 5079168823.0   50951108008.55 50951108008.56 50977580352.12651095978298.4  5114850435.127 51234361003.12851678667180.12451862169588.24652074235542.21052151318827.12652319338946.33 52432335730.24852523015483.26352575291859.24752575291859.24852577538839.25852577538839.26652577538839.26752577538839.26852577538839.29352819764660.25852877258371.3  52978530989.24853028877591.4  53184632406.26253223416603.33 53257845651.20 53508216722.21053529526209.26753661502701.26653767577775.12553926293342.25 53926293342.26 54110583096.8  54455947213.17 54480643220.26854788033261.26655019523437.26855053520205.17 55081428871.24955083526051.23255384490946.17 55504905889.0  55553571949.26856008580081.25656034671341.26656170256219.21256170256219.22956170256219.24656174447011.7  56179074418.24856765693369.24656765693885.19856771238972.21256773336117.20956843158307.23156845255431.24856974097633.52 56974097633.53 56980320960.12856994771444.2935703377594.20  57450526979.4  57548921327.29357628698627.11 57628698627.6  57628698627.8  57699555840.10 57701672254.24757701672383.24657709577267.23457709577278.20657740518026.10 57765562098.24757795177330.24857885813324.24857904412609.26758025198450.24858143249301.2  58197446068.25858249443405.17 58398153074.24858477402019.23258479499143.24958628372916.2585867961120.37  5867961120.38  58718705985.26759048690994.3  59052983343.4  59155188148.25859192637571.12459308628179.8  59308629082.4  59314873579.11 59314873579.8  59409783666.24859586081466.26659588178609.14259723945897.22 59825920688.24759847502578.24759994940353.26760109065581.26860546008002.33 6074268551.249 60759099917.7  6076365731.232 60869007213.26860974677274.25261001558721.26761094588916.29361208149259.3  61305990311.12461460999245.17 61560206755.23161562303879.24861779215085.26661917199023.12562083673382.22 62128165194.18 62128165194.19 62232972069.20 62232972069.26 62250799188.23062252498992.4  62302209411.12662445368724.25 62445368724.26 62595951604.2936265323769.33  6281403290.252 62885933440.4  62892351972.23062999281728.12663006859994.25263049147592.23063063700652.4  63068058720.64 63068058720.65 63235321900.12363348234032.24863375992104.26463378089262.2686341393216.127 63480717402.25263622150337.26763634301146.25263794685976.2676383882098.248 63922752810.23063937043790.6  63972618880.17 64022359336.38 64342530482.26864347751745.26764674898864.3  64772824451.12564797795698.24864864543962.25264875830376.7  65095166637.22 65106454934.13065128844401.26 65190585818.25265212743211.1286539704257.267 65461586437.2  65507993774.26865510090920.26465529901305.33 65566963629.1  66093981449.29266260595083.6  66275661716.25 66275661716.26 66336522568.6  66384610162.24866435675911.24866437773091.23167105517212.24967381608175.19 6744704702.268 67466105445.2576746801845.267 6746801847.265 6746801848.264 67475915204.26867481390445.26867532237250.17 67567392795.4  67680999037.14067800019075.12767818022492.25767820119639.2606798355636.18  6798355636.19  68137721793.26768254437966.20 68254437966.37 68254437966.38 68311500677.17 68317042083.23168319139207.2486837795181.268 68459412729.33 7130566823.126 7203867998.25  7203867998.26  745230189.268  7486304935.127 7611240667.7   7648604596.258 7654287582.264 7850740698.252 7895026546.248 8143751386.252 8265267294.0   8316209498.252 8448910976.17  8469793242.252 848608446.258  848608446.266  848608446.267  848608446.268  8595948977.142 8603416747.127 8608697946.252 8806422860.11  8806422860.12  8806422860.13  8806422860.8   8806422860.9   883891058.248  8892840775.249 8894937955.232 8935173664.270 8935173666.268 8937270825.267 8937270827.265 8957424365.266 9197910491.6   9407548634.252 9471306659.232 9473403783.249 9638965854.247 9829218171.261 9982983156.293 00000100@00M00\01P02D02J02P02Q02Z02[02_02`02a02b02c02d03<03E03T04:04;04?04@04A04G04R04X04^04m05<05K05Z06@06f06g07007107S07\07e07j08208U08Y08Z08[08a08g08m09\0:G0:P0:Q0:R0:X0:]0:b0:g0:m0:n0:o0;40;90;B0;H0;Q0;W0;\0;a0;b0;c0;d0<G0<j0=X0=]0=b0=g0=k0>60>70>?0>I0>M0>N0>T0>Y0>_0>e0>k0?10?20?60?M0?o0@80@B0@C0@D0@E0@k0A>0AC0AD0AM0AQ0AR0AS0AT0AU0AV0A\0Ah0B70BF0CM0DT0DU0DV0ED0F20F;0G10Gg0Gl0Gm0Gn0Go0H90HB0HP0HQ0Hc0I50I;0IJ0IS0IT0IZ0Ic0Ii0J<0Jb0KH0K[0Ka0Kb0Kf0Kk0Kl0L10L60L@0LO0L^0Lc0M80M<0MG0MK0MP0MV0MW0M]0O90O_0Pd0QN0QO0QP0Qb0Qc0Qd0Qe0Qf0Qj0R00R;0RA0RE0RI0RJ0RK0RL0RM0RS0RX0R]0R^0R_0Rd0Rj0Ro0S50S@0SA0SB0SH0SQ0SV0S_0S`0Se0Sj0Sk0T10T60T;0TE0TX0Tc0Td0Th0Ti0U20U60U?0UC0UI0U\0VB0VK0V]0Vo0W00W10WP0Wo0X40X50X;0XD0XI0XW0XX0XY0XZ0X_0Xh0Y60Y?0YQ0YR0YS0Y]0Yg0ZA0Z[0Z\0Za0Zj0Zn0[L0[j0\00\10\20\E0\k0]90]?0]R0^80^90^:0^>0^?0^@0^E0^J0^O0^S0^Y0^_0^h0_40_:0_E0_F0_G0_H0_Q0`00`;0`<0`=0`>0`H0`n0aA0aP0a_0ac0b20b>0bJ0bV0bZ0b[0bf0bg0c00c10c60c;0c?0cE0cJ0cP0cV0cW0cX0cY0c_0c`0ck0cl0d>0dC0dD0dM0dS0dY0dZ0dm0eS0eT0eU0eV0eW0eX0eY0eZ0e[0ee0ej0ek0f70f;0f<0fE0fK0fQ0fW0f\0fb0fc0fd0fe0ff0gE0gd0ge0gf0gg0gh0gi0gn0h70hF0hT0h_0hh0hi0ho0i>0iM0iV0iW0ii0jO0jb0jh0k70kI0k[0km0l30lL0lW0lX0lY0lZ0l[0li0lj0lk0ll0lm0m10m60m70m=0m>0mD0mL0mW0mh0n90n_0o20o70o<0oB0oH0oI0oJ0oP0oT0oZ0o[0o\0o]0of0og0oh0om0on0oo10510[10n11211811>11d12712@12U12j13313B13Q13Y13_13e13j13k14?14@14R14_15215E15k16Q16R16c17417F17^17_17e17f18118W18j19`19a19e19j19o1:41:91:>1:?1:E1:T1;<1;F1;P1;Z1;`1;i1;j1;o1<51<:1<I1<X1<g1=>1=U1=a1=j1>31>91>H1>I1>R1>S1>T1>U1>V1?D1?L1?T1?_1?d1?j1?o1@01@^1AL1AP1AU1AV1A[1A_1A`1Aa1Af1B11B:1B;1B<1B=1B>1BC1BH1BM1BN1BO1BV1Bc1Bj1Bo1CD1CE1CF1CL1CR1CV1Ce1D41D51D61DH1DN1DT1D_1EE1EX1Ec1Ed1Ej1Ek1F11F61F;1F@1FA1FJ1FY1Fh1G71GF1GY1H?1H@1HA1HE1HF1HP1HQ1H\1Hd1Hh1I01IA1I]1J91JU1K11K@1KI1KR1KS1KY1Kb1Kc1Kd1Ko1L81LK1M11M21ML1Mf1Ml1N11N81N91N:1NB1NJ1NY1N`1Ni1Nj1Nk1Nn1O41O=1OC1OI1OT1P:1P;1PN1PT1Pc1Pi1Pj1Po1Q01Q;1QN1R41R:1R>1RJ1RN1RR1RV1RZ1R[1R\1R]1Rc1Ri1Rj1S41SC1SD1SE1SI1SX1SY1SZ1TN1U<1U@1UF1UG1UH1UL1U[1Ua1V01VB1VK1V[1V\1Vb1W51W61W<1WA1WB1WK1WZ1W`1Wc1X11X21XA1XF1XL1XO1XP1XQ1X[1X\1X]1X^1Xd1Xj1Xk1Y41YZ1Ym1Yn1Z:1Z;1ZD1ZE1ZF1ZG1ZP1ZV1Za1Zb1Zc1Zd1Ze1Zj1Zm1[71[=1[P1[c1\61\K1\^1]D1]J1]T1]U1]d1^31^91^:1^E1^F1^K1^Z1^c1_21_31_B1_H1_W1_X1_Y1_Z1_[1_\1_a1`01`81`D1`L1`P1`T1`]1aC1aV1aW1aX1aY1aZ1a`1aa1b01bC1bi1bn1c31c4SS4CEIL2LO1H3HspS4CEIL2LO3CX1S4CEIL2LO1H3HspS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S4AHIaS4AHIaSS3LSJ3TICSS2LOSSSSSS4CEIL2LO3CX13Hsp2T13LSJS3LSJ3TICS3NSR3MSB3CWF1YS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14SS2HBFFS4AHIaS4CEIL2LO1HS4AHIaS4AHIaS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14SS3NSR3NSBFS3NSR4PA0b4PA0c3MSB3CWF3SH13SH22LTS3LSJ3TICS3LSJ3TICS3AALS3AAL2A0S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S2A0SSS4AHIaS4AHIaS4AHIaS4CEIL2LO3LSJ3MSB2A04AHId3SZP3SH54ASDa4ASDb3HspS4CEIL2LO3LSJ3MSB2A04AHId3SZP4ASDa4ASDb3HspS3LSJ3TICFFS4AHIaS3LSJS3LSJS3MSBS4AHIaSSS3LSJS3CWFS3LSJ3TICS4AHIaS3LSJ3TICS4AHIaS3AALS3HspFSSS4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23SH53HspS3LSJS3LSJS3NSRS2LOS4CEIL2LO1HSS4AHId1HS3NSR4PA0aS2LOSS4AHIaS3MSBS4CEILS4CEILS4CEILS4CEILSS2HBS3MSB4AHIb4AHIc3SH13SH2S4CEIL2LO3LSJ3MSB2A01H3SZP3SH23HspS3LSJ3TICS3NSR4PA0aFFSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3SPRSS3LSJ3TICS2T1FFFFFS4AHIaS4CEIL2LO2T1S4CEIL2LO1H3HspS4CEIL2LO3CX11HS4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0S4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0SSS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3LSJ3TICS3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3LSJFFSS3NSR4PA0aS3LSJ3TICS3NSR3CWF2LT1YSS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdS4AHIaS4CEIL2LO1H3HspS3LSJ3TICFS4AHIaS3LSJ3TICS4AHIaS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4AHIaSS2HqS3MSBSS3TICS3TICS3NSR4NRB0S3NSR3MSB3CWF1YS4CEIL2LO1H3HspS3HspS4CEIL2LO4PA0d3CWF2LTS2HBS4CEIL2LO1HS2HBS3HspS4AHIaSS4AHIaS4CEIL2LO3LSJ2NB3RSR3NSE3MSR3MSB2A01H3SZ83SZP3SH23SH53Hsp3CX13SH15CBNDa5CBNDb2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSB2A01H3SZP3SH23SH53HspS4CEIL2LO3CX13LSJ3MSB2A03SZP3SH13SH25CBNDa5CBNDb3Hsp1H2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23HspSSS4CEIL2LO4PA0d3CWFFFSSS2HBS4AHIaS4CEIL2LO1HS4AHIaS2LOS2HBSSSSS4AHIaS3LSJS3CX1FFS3SPRS4AHIaS3MSBS4AHIaS4CEIL2LO1HFSS4AHIaS3NSR3NSBS3SPRS3LSJ3TICSS3SH1S3SH1SS4AHIaS3NSRS3MSMS3NSR4PA0aS4CEIL2LO3MSB3SH21HS4CEIL2LO1HSS2A0SS3NSB1Y1ES2HBS3LSJ3TICS2HBS4AHIaS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3LSJ3TICS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdSSS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3SPRFS4AHIaS3LSJ3TICS3SZPS3NSR4NRB03NSBSSSS3MSBS3LSJ3TICS1N2NB3RSR3NSES3MSR3MSBS4CEIL2LO3MSB4AHIdSSS3NSR4PA0aS3NSR4PA0aS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0SS3AALS3LSJ3TICS2HBS3MSR3MSB4ASDa4ASDb1H2H02H42H5S3MSR3MSB4ASDa4ASDb1H2H02H42H5S4AHIaSSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO4AHIdS4AHIaS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSFS2LOFFS3MSBS3MSBS3AALS2A0S4AHIaS4AHIaS3LSJ3TICS4CEIL2LO2T1S1Y2Y0S4CEIL2LO1HFFFS3AAL3SZ8S3MSB3AAL2A04AHIa3SZ83SZP3MSR1YS4CEIL2LO1HSSSS3NSR4PA0aS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3MSB2A04AHId1HS4CEIL2LO1H3HspS2A0S4CEIL2LO1H3HspS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S2LOSS4CEIL2LO1HFS3LSJ3TICSS3SH1S3SH1S2LOS4AHIaS3MSBS4AHIaS4AHIaFFSS4AHIaSS4CEIL2LO1HSS4CEIL2LO3MSB4AHIdS3LSJSS3LSJ3TICS4AHIaS4AHIaSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSSSSSSSSS3NSR4PA0aS3SZPSS4PA0d3CWF1HS2LOSS3LSJ3TICS4AHIaS4AHIaS4AHIaS3HspS4AHIaSSSSS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFSSSSSS3TICS3LSJ3TICS3MSB2A04AHId1HS3MSB2A03ACE1HS4CEIL2LO1HS3LSJ3TICSS4AHIaS3SZ83SZP3SH11HS3SZ83SZP3SH11HS3LSJ3TICSS4CEIL2LO3MSB4AHIdS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4AHIaS4CEIL2LO3SPR1HS4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0S4AHIaS3MSB3SH13SH25TBNDa5TBNDbS3MSR3SZ81YSSFFS4CEIL2LO2AH1HSSFSS2LOS3SPRSS2T11HSS4AHIaS3NSR2KQS4CEIL2LO1HS4PA0a3MSB4AHIa1YS4PA0a3MSB4AHIa1YS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3SPRS3SPRS4AHIaS4AHIaFFS4AHIaS2LOS4AHIaSSSS3LSJ3TICFFS3AALSSS4AHIaS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS2HBS4AHIaS4AHIaS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3LSJ3TICS4CEIL2LO4PA0d3CWF2LTS4CEIL2LO4PA0d3CWF2LTS3LSJ3TICS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS3NSR2KQS4AHIaS4AHIaS3MSRSS3LSJ3MSB2A03SZP3SH5FS4CEIL2LO4PA0d3CWFS5TBNDa5TBNDbS4CEIL2LO1H3SH13HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSS3MSB4AHIa4AHId1HS3MSB4AHIa4AHId1HS3NSR3MSB2KQ3CWF1YS3NSR4PA0a3MSB3CWF2LT2Y0SS4AHIaSS4CEIL2LO1HS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS3NSR4PA0b4PA0c3MSR3MSB3CWF3SZ83SH13SH23SH52LT1Y2H42H9SS2LOS3MSBS3MSBS3MSBS3MSBS3MSBSS4AHIaS4CEIL2LO1H3HspS3MSR3MSB3SH13SH25TBNDa5TBNDb1H2H02H42H5S3NSR4NRB0S3NSR4NRB0S3NSR4NRB0S4AHIaS3LSJ3TICSS3CXIS4AHIaS3CXIS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS4CEIL2LO1H3HspS3MSB4AHIb4AHIc3SH13SH2S3MSB4AHIb4AHIc3SH13SH2S3MSB4AHId1HS3LSJ3TICS3LSJ3TICS4AHIaS4CEIL2LO1H3HspSS3LSJ3TICSSSSS3MSR3MSB3SZ83SH13SH25TBNDa5TBNDb1Y1H2H42H52H9S4AHIa1YS4AHIa1YS4CEIL2LO1HS3SPRS4AHIaS3SPRSS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S2HBS3MSBSS3SPRS2LOSFS3SPRS4CEIL2LO1HS3LSJ3TICSSSSS3MSBS3MSBS3MSBSSS1N3RSRS5TBNDa5TBNDbS3CX11HS3MSBS4CEIL2LO4PA0d3CWF2LTSSS4AHIaS4AHIaS2LOS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YFSS4CEIL2LO3MSB4AHIdS4AHIaS4AHIaS4CEIL2LO1HS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1HSS4AHIaSS4AHIaS3HspS3HspS3HspSS3LSJ3TICS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspFFS2HBSS3NSR4PA0aFS4CEIL2LO1HS3CWF2HqS2HqS3CWF2HqS2K02A03ACE3SZP1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS3MSR3MSB3SZ81YS3LSJ3TICS3LSJ3TICSS4AHIaS3LSJ3TICSSS4CEIL2LO1HS3LSJ3TICS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0S4AHIaS3CWFS3NSB1YSSS3MSR2K0S3MSB2K7S3SZP2K53MSR2K6S2A02K1S3LSJ3TICSSS1YS2T11HS3LSJ3TICS4AHIaS4AHIaS4CEIL2LO1HS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspFS4CEIL2LO1H3SH13HspS4AHIaS4CEIL2LO1H3HspS4AHIaSS3HspSS4CEIL2LO1HS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4AHIaS2LOS3MSB4AHIa1YS2LOS2LOS2LOS2LOSSSS4AHIaS4AHIaSS3NSR4PA0aS4CEIL2LO1H3HspFFS2HBS4CEIL2LO1H3HspFFS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H9S2LOS2T11HSSS2HBS4CEIL2LO1H3HspS4AHIaS4CEIL2LO1H3HspS4CEIL2LO3MSB4AHIdS3LSJ3TICS3LSJ3MSB2A03SZPFS4AHIaS3NSR4PA0a3CWF2LT1YSS4AHIaS3HspSS3LSJ3TICS4CEIL2LO1H3HspS4NRB0S1YS1N2NB3RSR3NSESS4CEIL2LO1H3HspS3SPRS4AHIaS1YSSS3NSR4PA0aSSFS4AHIaS4AHIaFS3LSJ3TICS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspSS3NSR2KQ3CWFSS3NSR3NSBSSSS3NSR3NSBS4AHIaS4CEIL2LO1HFFSSS3LSJS1YS3NSR2KQ1YS4AHIaS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HS3AAL4AHIa4AHId3SZ81YS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4AHIaS3NSR4PA0aSS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS4AHIaSS4CEIL2LO1HSS3MSBS4CEIL2LO1H3HspS3LSJ3TICS4CEIL2LO1H3HspSS4CEIL2LO1H3HspS4AHIaS4CEIL2LO1H3HspSSSSSS3SPRS4CEIL2LO1H3HspS3CWF2HqS3MSB3CWF2HqS3MSB2HqS2HqS2HqS3LSJ3TICS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspFFFFS4AHIaFS4CEIL2LO1H3HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3SH5S3LSJS".
assert (MS4 : exists q, ms = 4096 * q) by (exists (ms / 4096); clear -MSM MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  clear RSE. box MSE. box RSM. box MSM. box NRM. box PAL. box CT2. box DPT. box DPC.
  (* [comment removed for export] *)
  iprefix.
  carve_frame 96%nat ST.
  do 12 step.                                                  (* [comment removed for export] *)
  assert (HWL : Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv)) \/ (0x9d870 <= fst iv /\ snd iv <= 0xa0080))
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
  assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
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
  assert (JSL2 : nsec < nres -> rw_cells asegs m2 (PA + 8 * nsec) [CB 8 jslot]).
  { intros LT. specialize (JSL LT). xport JSL MUA WMA ltac:(ub DAP; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT Y; dlia). exact JSL. }
  clear JSL.
  (* [comment removed for export] *)
  change (rw_cells asegs m2 (shad a) [CB (Z.to_nat (ms / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms / 8)))]) with (fill_at m2 (shad a) (ms / 8) 0) in SH0.
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
  replace (ret_pc (Z_to_bv 64 219732)) with (Z_to_bv 64 219732 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
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
                          (0x9d888, 0x9dae8); (t + 2800, t + 3168);
                          (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z) in MUA.
  2: { unfold sub_fp. cbn [outside]. clear. intros q Hq. tauto. }
  (* [comment removed for export] *)
  unfold fill_at in SHH, SHU, SHT.
  pose proof PC2 as PCx. destruct PCx as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  pose proof RC2 as RCx. destruct RCx as (Q1 & Q2 & Q3 & Q4 & Q5). clear PC2 RC2 Q3.
  Local Ltac pcells := unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption.
  (* [comment removed for export] *)
  assert (RSH1 : rng RNG' (shad a) 512) by (eapply rng_sub'; [exact RSCH|]; clear -MSB; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad a, shad a + 512)]%Z m2) as MUS. pose proof (wmono_refl asegs m2) as WMS.
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
  lazymatch goal with M : munch _ m2 ?mm, W : wmono asegs m2 _ |- _ =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
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
    pose proof (wmono_refl asegs mm) as WMS end.
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
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(ub MSM; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 SH5 MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; dlia); exact JSL2);
    clear JSL2 M W; rename JSL3 into JSL2 end.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96)]%Z mm) as MUS; pose proof (wmono_refl asegs mm) as WMS end.
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
  lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT; dlia); exact JSL2);
    clear JSL2; rename JSL3 into JSL2;
    (* [comment removed for export] *)
    apply (munch_weaken _ [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96); (t + 2872, t + 2888)]%Z) in M;
    [ rename M into MUS2; rename W into WMS2 | unfold sub_fp; cbn [outside]; clear; intros q Hq; tauto ] end.
  clear CT.
  (* [comment removed for export] *)
  snapshot [(t + 2872, t + 2888); (a, a + 32); (0x9dac0, 0x9dac4)]%Z MUz WMz.
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
    assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
      by (intros LT; specialize (JSL2 LT); xport JSL2 MUz WMz ltac:(ub DPT; ub DAP; clear -Y Y0 SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT T1 AHI AHIa AHIb AHIc AHId ACE MSB TIC; dlia); exact JSL2);
    clear JSL2 MUz WMz; rename JSL3 into JSL2 end.
  box STATS. box ZP. box ZU. box POST. box POST0. box SHU.   (* [comment removed for export] *)
  snapshot [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + 32); (0x9d888, 0x9dae8);
            (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z MUr WMr.
  snapshot [(a, a + 32); (0x9dac0, 0x9dac4)]%Z MUq WMq.      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  step. if_cases K7; zify_cond K7. { exfalso. clear -K7 MSB. lia. }                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 645824) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
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
      assert (WMr2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMr | exact WMc]) end.
    clear MUr WMr. rename MUr2 into MUr. rename WMr2 into WMr.
    lazymatch type of MUA with munch ?Wa ?ma ?mb =>
      assert (MUA2 : munch Wa ma mc) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
      assert (WMA2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMA | exact WMc]) end.
    clear MUA WMA MUc WMc. rename MUA2 into MUA. rename WMA2 into WMA.
    apply (rng_fp_le _ _ _ _ FPLE2) in RIMG. apply (rng_fp_le _ _ _ _ FPLE2) in RSTK. apply (rng_fp_le _ _ _ _ FPLE2) in RCH.
    apply (rng_fp_le _ _ _ _ FPLE2) in RSCH. apply (rng_fp_le _ _ _ _ FPLE2) in RPA.
    iprefix.
    replace (ret_pc (Z_to_bv 64 220660)) with (Z_to_bv 64 220660 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
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
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    xport ZCR MU9 WM9 ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0x9d888, 0x9dae8); (t + 2800, t + 3168);
                         (PA + 8 * nres, PA + 8 * nres + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT2 a RNG'' m9); [exact HFR | reflexivity |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [eapply fp_le_trans; [exact FPLE| exact FPLE2]|]. split; [exact BW2|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nres)] [CB _ _])).
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
      assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
    clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
    carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
    carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
    carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).   (* [comment removed for export] *)
    carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
    assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
                         (0x9d888, 0x9dae8); (t + 2800, t + 3168);
                         (PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
    assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
    eapply (KONT1 a RNG' m9); [exact HFR | exact KQ |].
    unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
    split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
    split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
    split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)] [CB _ _])).
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
