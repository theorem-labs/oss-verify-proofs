(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the launch facts the plain binary's library is closed under
   ([ECH_LibTop.vdso_run_facts]), proved from the launch.  The run's tail is the vDSO/vvar pair
   [Run.vdso_segments kb sp mbase] (Run.v:290-306 at 20f40762); [vd_lo], [vd_mid] and [vd_top] are the
   pair's base, text base and top as that function computes them.  On a valid stack pointer and mmap
   base the pair is the vvar segment [[vd_lo, vd_mid)] and the text segment [[vd_mid, vd_top)], both
   "r--", the text holding the measured image ([Lib/VdsoImg.vdso_image_of_const]); the binary's own
   segments end below 0x311000 ([RMallocRep.ref_find_segment_none]).
   - [Run.vdso_segments] is Global Opaque (Run.v:308-322): [vdso_segments_two] is the one lemma that
     opens it, as the model's Checks/Cases/Kernel/Vdso.v does.  The image's bytes are reduced only by
     two closed checks, each of which yields a boolean or a short term: [image_of_bytes_self] (the
     twelve chunks compared with themselves, as [RiscvSemantics.vdso_image] recognises the image) and
     [rvdso_cover_check] (every offset below the image's size has a byte, which [Lib/VdsoImg.rvdso_rom]
     reads through [rvdso_peek]).
   - The auxv publishes AT_SYSINFO_EHDR as [Run.vdso_text_base kb sp mbase], the text base of the pair
     the run maps: the pair's top [Run.vdso_pair_top] less the text pages (Run.v:299-310 at b84e73ef),
     the same address [Run.vdso_segments] places the text at.  [vdso_text_base_pair] reads it as
     [vd_mid] on every valid launch; every other fact uses only its equation. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Vdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec Mem VdsoImg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RVdsoSegs ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require RMallocRep.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MmVdso.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** * The pair's addresses and segments, as [Run.vdso_segments] builds them *)

Definition vd_top (sp mbase : word) : Z :=
  page_round_down_Z (Z.min (bv_unsigned mbase) (page_round_down_Z (bv_unsigned sp - stack_max_size))).
Definition vd_lo (kb : KernelBuild) (sp mbase : word) : Z := vd_top sp mbase - vdso_len kb.
Definition vd_mid (kb : KernelBuild) (sp mbase : word) : Z := vd_top sp mbase - vdso_text_pages kb * page_size.

Definition vv_seg (base : Z) : Segment :=
  {| seg_base := Z.to_N base; seg_size := Z.to_N (vdso_vvar_pages * page_size);
     seg_perms := "r--"%string; seg_bytes := []; seg_kind := SegVdsoVvar |}.
Definition vt_seg (kb : KernelBuild) (tbase : Z) : Segment :=
  {| seg_base := Z.to_N tbase; seg_size := Z.to_N (vdso_text_pages kb * page_size);
     seg_perms := "r--"%string; seg_bytes := vi_bytes (vdso_image_of kb); seg_kind := SegVdsoText |}.

Section VdsoPairForm.
  Local Transparent vdso_segments.

  (* the two segments of Run.v:312-325 at b84e73ef, when the ledger reserves the pair; the text's
     base is [bv_unsigned (Run.vdso_text_base kb sp mbase)], which is [vd_mid] there *)
  Lemma vdso_segments_two : forall kb (sp mbase : word), page_size <= vd_lo kb sp mbase ->
    vdso_segments kb sp mbase = [vv_seg (vd_lo kb sp mbase); vt_seg kb (vd_mid kb sp mbase)].
  Proof.
    intros kb sp mbase H.
    assert (HB : bv_unsigned (vdso_text_base kb sp mbase) = vd_mid kb sp mbase).
    { change (vdso_text_base kb sp mbase) with (Z_to_bv 64 (vd_mid kb sp mbase)).
      apply bv_unsigned_Z_to_bv_u64.
      pose proof (page_round_down_Z_le
                    (Z.min (bv_unsigned mbase) (page_round_down_Z (bv_unsigned sp - stack_max_size)))) as P.
      pose proof (u64_range mbase) as R.
      assert (TP : 0 <= vdso_text_pages kb) by (unfold vdso_text_pages; lia).
      unfold vd_lo, vd_mid, vd_top, vdso_len, vdso_vvar_pages in *. unfold two_pow_64, page_size in *. lia. }
    unfold vdso_segments. cbv zeta. rewrite HB.
    match goal with |- (if ?b then _ else _) = _ => destruct b eqn:E end.
    - exfalso. apply Z.ltb_lt in E. unfold vd_lo, vd_top in H. unfold vdso_pair_top in E. lia.
    - reflexivity.
  Qed.
End VdsoPairForm.

(** * Facts about any segment list *)

Lemma find_two_raw : forall kb (b t x n : Z),
  find_segment [vv_seg b; vt_seg kb t] x n =
  if andb (Z.leb (Z.of_N (seg_base (vv_seg b))) x)
          (Z.leb (x + n) (Z.of_N (seg_base (vv_seg b)) + Z.of_N (seg_size (vv_seg b))))
  then Some (vv_seg b)
  else if andb (Z.leb (Z.of_N (seg_base (vt_seg kb t))) x)
               (Z.leb (x + n) (Z.of_N (seg_base (vt_seg kb t)) + Z.of_N (seg_size (vt_seg kb t))))
  then Some (vt_seg kb t)
  else None.
Proof. intros kb b t x n. reflexivity. Qed.

Lemma find_app_none : forall (A : Type) (f : A -> bool) (l1 l2 : list A),
  List.find f l1 = None -> List.find f (l1 ++ l2) = List.find f l2.
Proof.
  intros A f l1 l2. induction l1 as [|y l1 IH]; intros H; [reflexivity|].
  revert H. cbn [List.find app]. destruct (f y); [intros H; discriminate H | exact IH].
Qed.

Lemma memory_read_found : forall segs (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_readable seg = true ->
  memory_read segs a 1 = segment_read_bytes (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) 1.
Proof.
  intros segs a seg Hf Hr. unfold memory_read. change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta.
  rewrite Hr. reflexivity.
Qed.

Lemma ro_addr_found : forall segs (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> ro_addr segs a = negb (seg_writable seg).
Proof. intros segs a seg Hf. unfold ro_addr. rewrite Hf. reflexivity. Qed.

Lemma vdso_text_at_found : forall segs (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> vdso_text_at segs a = seg_vdso_text seg.
Proof. intros segs a seg Hf. unfold vdso_text_at. rewrite Hf. reflexivity. Qed.

Lemma code_read_found : forall segs (a : word) (n : N) seg,
  find_segment segs (bv_unsigned a) (Z.of_N n) = Some seg -> seg_executable seg = false ->
  code_read segs a n = None.
Proof. intros segs a n seg Hf Hx. unfold code_read. rewrite Hf. cbv beta iota zeta. rewrite Hx. reflexivity. Qed.

Lemma code_read_ov_found : forall segs m (a : word) (n : N) seg,
  find_segment segs (bv_unsigned a) (Z.of_N n) = Some seg -> seg_executable seg = false ->
  code_read_ov segs m a n = None.
Proof. intros segs m a n seg Hf Hx. unfold code_read_ov. rewrite Hf. cbv beta iota zeta. rewrite Hx. reflexivity. Qed.

Lemma srb1 : forall bs off,
  segment_read_bytes bs off 1 = match segment_byte_at bs off with Some b => Some [b] | None => None end.
Proof. intros bs off. cbn [segment_read_bytes]. destruct (segment_byte_at bs off); reflexivity. Qed.

(** * The measured image *)

(* the binary's own segments hold no vDSO text, as [MainSegs.vdso_image_RSEGS] *)
Lemma find_text_rsegs : List.find seg_vdso_text rsegs = None.
Proof. reflexivity. Qed.

(* [RiscvSemantics.vdso_image] recognises the text's bytes as the measured image: the twelve chunks
   compared with themselves *)
Lemma image_of_bytes_self : vdso_image_of_bytes vdso_images (vi_bytes RVDSO_IMAGE) = Some RVDSO_IMAGE.
Proof. reflexivity. Qed.

(* every offset below the image's size has a byte *)
Fixpoint rv_all_some (bs : list PrimString.string) (o : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match segment_byte_at bs (Z.to_N o) with
            | Some _ => rv_all_some bs (o + 1) n'
            | None => false
            end
  end.

Lemma rv_all_some_ok : forall bs n o, rv_all_some bs o n = true ->
  forall k, 0 <= k < Z.of_nat n -> segment_byte_at bs (Z.to_N (o + k)) <> None.
Proof.
  intros bs n. induction n as [|n IH]; intros o H k Hk; [lia|].
  revert H. cbn [rv_all_some].
  destruct (segment_byte_at bs (Z.to_N o)) as [b|] eqn:E; intros H; [|discriminate H].
  destruct (Z.eq_dec k 0) as [->|Hk0].
  - rewrite Z.add_0_r, E. discriminate.
  - replace (o + k) with ((o + 1) + (k - 1)) by ring. apply IH; [exact H|]. lia.
Qed.

(* A closed check over the 5704 offsets; its value is a boolean, so no normal form holds the bytes. *)
Lemma rvdso_cover_check : rv_all_some (vi_bytes RVDSO_IMAGE) 0 (Z.to_nat RVDSO_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rvdso_cover : forall o, 0 <= o < RVDSO_SIZE -> segment_byte_at (vi_bytes RVDSO_IMAGE) (Z.to_N o) <> None.
Proof.
  intros o Ho E. pose proof RVDSO_SIZE_val as HS.
  assert (Hk : 0 <= o < Z.of_nat (Z.to_nat RVDSO_SIZE)) by (rewrite Z2Nat.id by lia; lia).
  exact (rv_all_some_ok (vi_bytes RVDSO_IMAGE) (Z.to_nat RVDSO_SIZE) 0 rvdso_cover_check o Hk E).
Qed.

Lemma rvdso_byte_some : forall o, 0 <= o < RVDSO_SIZE ->
  segment_byte_at (vi_bytes RVDSO_IMAGE) (Z.to_N o) = Some (rvdso_byte o).
Proof.
  intros o Ho. pose proof (rvdso_cover o Ho) as C. unfold rvdso_byte.
  destruct (segment_byte_at (vi_bytes RVDSO_IMAGE) (Z.to_N o)) as [b|] eqn:E; [reflexivity|].
  exfalso. apply C. reflexivity.
Qed.

Local Ltac vl_zbool :=
  repeat match goal with
         | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
         | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
         end.

(** * The launch's pair *)

Section Launch.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variable kb : KernelBuild.
  Variables sp mbase : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hmb : valid_mmap_base mbase.

  Local Notation VLO := (vd_lo kb sp mbase).
  Local Notation VMID := (vd_mid kb sp mbase).
  Local Notation VTOP := (vd_top sp mbase).
  Local Notation VTAIL := (vdso_segments kb sp mbase).

  (* one measured image of two pages (Vdso.v:287-290) *)
  Lemma text_pages_2 : vdso_text_pages kb = 2.
  Proof. unfold vdso_text_pages. rewrite vdso_image_of_const. exact RVDSO_PAGES_val. Qed.

  Lemma len_24576 : vdso_len kb = 24576.
  Proof. unfold vdso_len. rewrite text_pages_2. reflexivity. Qed.

  Lemma top_facts : VTOP mod 4096 = 0
    /\ Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 8192 < VTOP
    /\ VTOP <= bv_unsigned mbase
    /\ VTOP <= bv_unsigned sp - stack_max_size.
  Proof. unfold vd_top, page_round_down_Z, page_size. Z.div_mod_to_equations. lia. Qed.

  Lemma top_range : 0x154555555000 < VTOP /\ VTOP <= 0x7ffff8000000.
  Proof.
    pose proof top_facts as (_ & T2 & T3 & T4).
    pose proof Hsp as (S1 & S2 & _). pose proof Hmb as (M1 & M2 & _).
    unfold mmap_base_max, mmap_base_min, sp_window_hi, sp_window_lo, stack_max_size in *.
    lia.
  Qed.

  Lemma lo_bounds : 0x311000 <= VLO /\ page_size <= VLO.
  Proof. pose proof top_range. unfold vd_lo. rewrite len_24576. unfold page_size. lia. Qed.

  Lemma lo_mid : VLO + 16384 = VMID.
  Proof. unfold vd_lo, vd_mid. rewrite len_24576, text_pages_2. unfold page_size. lia. Qed.

  Lemma mid_top : VMID + 8192 = VTOP.
  Proof. unfold vd_mid. rewrite text_pages_2. unfold page_size. lia. Qed.

  Lemma mid_al : VMID mod 4096 = 0.
  Proof.
    pose proof top_facts as (T1 & _). unfold vd_mid. rewrite text_pages_2. unfold page_size.
    Z.div_mod_to_equations. lia.
  Qed.

  Lemma tail_two : VTAIL = [vv_seg VLO; vt_seg kb VMID].
  Proof. apply vdso_segments_two. exact (proj2 lo_bounds). Qed.

  Lemma vv_base : Z.of_N (seg_base (vv_seg VLO)) = VLO.
  Proof. pose proof lo_bounds as [L _]. change (Z.of_N (Z.to_N VLO) = VLO). apply Z2N.id. lia. Qed.

  Lemma vv_size : Z.of_N (seg_size (vv_seg VLO)) = 16384.
  Proof. reflexivity. Qed.

  Lemma vt_base : Z.of_N (seg_base (vt_seg kb VMID)) = VMID.
  Proof.
    pose proof lo_bounds as [L _]. pose proof lo_mid. change (Z.of_N (Z.to_N VMID) = VMID). apply Z2N.id. lia.
  Qed.

  Lemma vt_size : Z.of_N (seg_size (vt_seg kb VMID)) = 8192.
  Proof. change (Z.of_N (Z.to_N (vdso_text_pages kb * page_size)) = 8192). rewrite text_pages_2. reflexivity. Qed.

  Lemma vt_bytes : seg_bytes (vt_seg kb VMID) = vi_bytes RVDSO_IMAGE.
  Proof. exact (f_equal vi_bytes (vdso_image_of_const kb)). Qed.

  Lemma vt_x : seg_executable (vt_seg kb VMID) = false. Proof. reflexivity. Qed.
  Lemma vt_w : seg_writable (vt_seg kb VMID) = false. Proof. reflexivity. Qed.
  Lemma vt_r : seg_readable (vt_seg kb VMID) = true. Proof. reflexivity. Qed.
  Lemma vt_t : seg_vdso_text (vt_seg kb VMID) = true. Proof. reflexivity. Qed.

  Lemma find_two : forall x n, find_segment VTAIL x n =
    if andb (Z.leb VLO x) (Z.leb (x + n) VMID) then Some (vv_seg VLO)
    else if andb (Z.leb VMID x) (Z.leb (x + n) VTOP) then Some (vt_seg kb VMID)
    else None.
  Proof.
    intros x n. rewrite tail_two, find_two_raw, vv_base, vv_size, vt_base, vt_size, lo_mid, mid_top.
    reflexivity.
  Qed.

  (* above the binary's segments, the run's list answers with the pair *)
  Lemma find_run : forall x n, 1 <= n -> 0x311000 <= x ->
    find_segment (rsegs ++ VTAIL) x n = find_segment VTAIL x n.
  Proof.
    intros x n Hn Hx. rewrite find_segment_app.
    rewrite (Ref.RMallocRep.ref_find_segment_none x n Hn (or_intror Hx)). reflexivity.
  Qed.

  Lemma find_text : forall x n, 1 <= n -> VMID <= x -> x + n <= VTOP ->
    find_segment (rsegs ++ VTAIL) x n = Some (vt_seg kb VMID).
  Proof.
    intros x n Hn H1 H2. pose proof lo_bounds as [L1 L2]. pose proof lo_mid as LM.
    rewrite (find_run x n Hn) by lia. rewrite find_two.
    vl_zbool; cbn [andb]; first [exfalso; lia | reflexivity].
  Qed.

  (** ** The image is read through the text segment *)

  Lemma mr_text : forall o, 0 <= o < RVDSO_SIZE ->
    memory_read (rsegs ++ VTAIL) (wa (VMID + o)) 1 = Some [rvdso_byte o].
  Proof.
    intros o Ho. pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top.
    pose proof top_range as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment (rsegs ++ VTAIL) (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply find_text; lia).
    rewrite (memory_read_found _ _ _ Hf vt_r), Hu, vt_base, vt_bytes.
    replace (VMID + o - VMID) with o by ring.
    rewrite srb1, (rvdso_byte_some o Ho). reflexivity.
  Qed.

  Lemma rom_text : forall o, 0 <= o < RVDSO_SIZE ->
    seg_rom (rsegs ++ VTAIL) (wa (VMID + o)) = rvdso_peek o.
  Proof. intros o Ho. unfold seg_rom. rewrite (mr_text o Ho), (rvdso_peek_in o Ho). reflexivity. Qed.

  Lemma ro_text : forall o, 0 <= o < RVDSO_SIZE -> ro_addr (rsegs ++ VTAIL) (wa (VMID + o)) = true.
  Proof.
    intros o Ho. pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top.
    pose proof top_range as [T1 T2]. pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (wa (VMID + o)) = VMID + o) by (apply wa_unsigned; lia).
    assert (Hf : find_segment (rsegs ++ VTAIL) (bv_unsigned (wa (VMID + o))) 1 = Some (vt_seg kb VMID))
      by (rewrite Hu; apply find_text; lia).
    rewrite (ro_addr_found _ _ _ Hf), vt_w. reflexivity.
  Qed.

  Lemma rom_pair : rvdso_rom (rvsegs VTAIL) VMID.
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top. pose proof top_range as [T1 T2].
    unfold rvdso_rom, rvsegs. rewrite RVDSO_SPAN_val.
    split; [lia|]. split; [exact mid_al|]. split; [lia|].
    intros o Ho. exact (conj (rom_text o Ho) (ro_text o Ho)).
  Qed.

  (** ** The machine declines at a pc in the text ([RiscvSemantics.fetch_failure]'s vdso_text_at
      arm, RiscvSemantics.v:1156-1180): no fetch path reads the "r--" text *)

  Lemma code_read_text : forall (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read (rsegs ++ VTAIL) a n = None.
  Proof.
    intros a n Hn H1 H2. exact (code_read_found _ a n _ (find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) vt_x).
  Qed.

  Lemma code_read_ov_text : forall m (a : word) (n : N), 1 <= Z.of_N n -> VMID <= bv_unsigned a ->
    bv_unsigned a + Z.of_N n <= VTOP -> code_read_ov (rsegs ++ VTAIL) m a n = None.
  Proof.
    intros m a n Hn H1 H2.
    exact (code_read_ov_found _ m a n _ (find_text (bv_unsigned a) (Z.of_N n) Hn H1 H2) vt_x).
  Qed.

  Lemma fw_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word (rsegs ++ VTAIL) a = None.
  Proof.
    intros a H1 H2. unfold fetch_word.
    rewrite (code_read_text a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma fwo_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 4 <= VTOP ->
    fetch_word_ov (rsegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_word_ov.
    rewrite (code_read_ov_text m a 4 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma fh_none : forall (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half (rsegs ++ VTAIL) a = None.
  Proof.
    intros a H1 H2. unfold fetch_half.
    rewrite (code_read_text a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma fho_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_ov (rsegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_half_ov.
    rewrite (code_read_ov_text m a 2 ltac:(cbn [Z.of_N]; lia) H1 ltac:(cbn [Z.of_N]; lia)). reflexivity.
  Qed.

  Lemma fha_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_half_any (rsegs ++ VTAIL) m a = None.
  Proof. intros m a H1 H2. unfold fetch_half_any. rewrite (fh_none a H1 H2), (fho_none m a H1 H2). reflexivity. Qed.

  Lemma fta_none : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 2 <= VTOP ->
    fetch_tail_any (rsegs ++ VTAIL) m a = None.
  Proof.
    intros m a H1 H2. unfold fetch_tail_any. rewrite (fha_none m a H1 H2).
    match goal with |- context [if negb ?b then _ else _] => destruct b end; reflexivity.
  Qed.

  Lemma ff_unm : forall m (a : word), VMID <= bv_unsigned a -> bv_unsigned a + 1 <= VTOP ->
    fetch_failure (rsegs ++ VTAIL) m a = MachineUnmodeled.
  Proof.
    intros m a H1 H2. unfold fetch_failure.
    rewrite (vdso_text_at_found _ a _ (find_text (bv_unsigned a) 1 ltac:(lia) H1 H2)), vt_t. reflexivity.
  Qed.

  Lemma unm_text : forall ms, ms_pc ms = Z_to_bv 64 (VMID + 1460) ->
    RiscvSemantics.step (rsegs ++ VTAIL) ms = MachineUnmodeled.
  Proof.
    intros ms Hpc. pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top.
    pose proof top_range as [T1 T2].
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold RiscvSemantics.step, RiscvSemantics.step_accesses. rewrite Hpc.
    rewrite (fw_none (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (fwo_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (fta_none (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    rewrite (ff_unm (ms_mem ms) (Z_to_bv 64 (VMID + 1460))) by (rewrite Hu; lia).
    reflexivity.
  Qed.

  (** ** The entry at text base + 1460 is clock_gettime's ([Lib/VdsoImg.rvdso_cgt_off_entry]) *)

  Lemma vimg : vdso_image (rsegs ++ VTAIL) = Some (vt_seg kb VMID, RVDSO_IMAGE).
  Proof.
    unfold vdso_image, vdso_text_seg.
    rewrite (find_app_none _ seg_vdso_text rsegs VTAIL find_text_rsegs), tail_two.
    change (List.find seg_vdso_text [vv_seg VLO; vt_seg kb VMID]) with (Some (vt_seg kb VMID)).
    cbv beta iota zeta. rewrite vt_bytes, image_of_bytes_self. reflexivity.
  Qed.

  Lemma ent_text : vdso_entry_fn (rsegs ++ VTAIL) (Z_to_bv 64 (VMID + 1460)) = Some VdsoClockGettime.
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top. pose proof top_range as [T1 T2].
    pose proof RVDSO_SIZE_val as HS.
    assert (Hu : bv_unsigned (Z_to_bv 64 (VMID + 1460)) = VMID + 1460) by (apply wa_unsigned; lia).
    unfold vdso_entry_fn. rewrite vimg. cbv beta iota zeta.
    rewrite vt_base, Hu.
    change (Z.of_N (vi_size RVDSO_IMAGE)) with RVDSO_SIZE.
    replace (VMID + 1460 - VMID) with RVDSO_CGT_OFF by (unfold RVDSO_CGT_OFF; ring).
    vl_zbool; cbn [andb]; first [exfalso; lia | exact rvdso_cgt_off_entry].
  Qed.

  (** ** The pair in the launch's reserved ledger ([State.vdso_reserved], State.v:6559-6564) *)

  Lemma vdso_reserved_pair : vdso_reserved kb VTOP =
    [(Z_to_bv 64 VLO, Z_to_bv 64 16384); (Z_to_bv 64 VMID, Z_to_bv 64 8192)].
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid as LM.
    unfold vdso_reserved. cbv zeta.
    change (VTOP - vdso_len kb) with VLO.
    rewrite (proj2 (Z.ltb_ge VLO page_size) L2).
    rewrite text_pages_2.
    replace (VLO + vdso_vvar_pages * page_size) with VMID by (unfold vdso_vvar_pages, page_size; lia).
    reflexivity.
  Qed.

  Lemma pair_win_lo : MmVdso.win_in VLO VMID (vdso_reserved kb VTOP).
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top. pose proof top_range as [T1 T2].
    unfold MmVdso.win_in. rewrite vdso_reserved_pair.
    exists (Z_to_bv 64 VLO, Z_to_bv 64 16384). split; [left; reflexivity|]. cbn [fst snd].
    rewrite !bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64; lia). lia.
  Qed.

  Lemma pair_win_hi : MmVdso.win_in VMID VTOP (vdso_reserved kb VTOP).
  Proof.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid. pose proof mid_top. pose proof top_range as [T1 T2].
    unfold MmVdso.win_in. rewrite vdso_reserved_pair.
    exists (Z_to_bv 64 VMID, Z_to_bv 64 8192). split; [right; left; reflexivity|]. cbn [fst snd].
    rewrite !bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64; lia). lia.
  Qed.

  (** ** AT_SYSINFO_EHDR and the text base ([Run.vdso_text_base], b84e73ef): the pair's text base on
      every valid launch *)

  Lemma vdso_text_base_pair : bv_unsigned (vdso_text_base kb sp mbase) = VMID.
  Proof.
    pose proof top_range as [T1 T2].
    change (vdso_text_base kb sp mbase) with (Z_to_bv 64 VMID).
    apply bv_unsigned_Z_to_bv_u64. unfold vd_mid. rewrite text_pages_2. unfold two_pow_64, page_size. lia.
  Qed.

  (** ** The record *)

  Theorem vdso_run_facts_of :
    hceil = bv_unsigned sp - stack_max_size ->
    hvdso = bv_unsigned (vdso_text_base kb sp mbase) + 1460 ->
    bv_unsigned (vdso_text_base kb sp mbase) = VMID ->
    vdso_run_facts VTAIL VLO VMID VTOP.
  Proof.
    intros HCE HVD HTB.
    pose proof lo_bounds as [L1 L2]. pose proof lo_mid as LM. pose proof mid_top as MT.
    pose proof top_facts as (_ & _ & T3 & T4).
    assert (HVB : hvdso = VMID + 1460) by (rewrite HVD, HTB; reflexivity).
    split.
    - exact (vdso_segments_nx kb sp mbase).
    - exact (vdso_segments_nw kb sp mbase).
    - reflexivity.
    - lia.
    - lia.
    - intros x s Hf. rewrite find_two in Hf. revert Hf.
      vl_zbool; cbn [andb]; intros Hf; first [discriminate Hf | lia].
    - intros x Hx. rewrite find_two.
      vl_zbool; cbn [andb]; first [discriminate | exfalso; lia].
    - exact rom_pair.
    - exact HVB.
    - rewrite HVB. exact ent_text.
    - intros ms Hpc. rewrite HVB in Hpc. exact (unm_text ms Hpc).
  Qed.

  Theorem vdso_launch_facts :
    hceil = bv_unsigned sp - stack_max_size ->
    hvdso = bv_unsigned (vdso_text_base kb sp mbase) + 1460 ->
    vdso_run_facts VTAIL VLO VMID VTOP.
  Proof. intros HCE HVD. exact (vdso_run_facts_of HCE HVD vdso_text_base_pair). Qed.
End Launch.
