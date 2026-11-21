(* SPDX-License-Identifier: MIT *)
(* The run's segment list.

   LPS 75d69e00 made [realizes] / [init_config] / [reaches_error] read
   the RUN's segment list [Run.run_segments segs inp sp mbase], which is
   the image's own LOAD segments followed by the vDSO pair
   ([Run.run_segments], LPS 75d69e00 theories/LinuxProcessSem/Run.v:328-330):

     run_segments segs inp sp mbase = segs ++ vdso_segments (in_kernel inp) sp mbase

   The image's segments come FIRST, and every reader the proof layer goes
   through — [find_segment] under [memory_read], [code_read],
   [code_read_wx] and [wview] — is a HEAD-FIRST linear scan returning the
   first covering segment (LPS 75d69e00
   theories/LinuxProcessSem/RiscvSemantics.v:332-345).  So a hit among the
   image's own segments is the SAME hit in any longer list, and every fact
   the harness proves by [vm_compute] over the image's own list carries
   over to the run's list unchanged.

   The four base lemmas below are the ones LPS states for exactly this
   purpose at 75d69e00
   theories/Examples/rwx_flag_ns/rwx_flag_ns_defs.v:106-140; the rest are
   the tree-level readers built on them.

   DIRECTION.  Every lemma here carries a SUCCESSFUL read (a [Some], a
   [true]) from the short list to the long one.  The opposite direction
   does NOT hold and is deliberately absent: a predicate asserting that an
   address is UNMAPPED ([find_segment segs a 1 = None], as in
   [St.region_ok]'s [ro_valid]) can be falsified by the extra vDSO
   segments, and must be discharged from the vDSO's placement
   ([Run.vdso_segments], LPS 75d69e00 Run.v:290-300), never by transport. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 Val IMap Mem State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import DrvLib DrvTop.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Module RunSeg.

(* ===================================================================== *)
(* The run's list is the image's list with the vDSO pair appended         *)
(* ===================================================================== *)

Lemma run_segments_eq : forall segs inp sp mbase,
  run_segments segs inp sp mbase = segs ++ vdso_segments (in_kernel inp) sp mbase.
Proof. intros segs inp sp mbase. reflexivity. Qed.

(* ===================================================================== *)
(* LPS readers: a hit in the head keeps its answer in any longer list     *)
(* ===================================================================== *)

Lemma find_segment_app : forall segs vt a n seg,
  find_segment segs a n = Some seg -> find_segment (segs ++ vt) a n = Some seg.
Proof.
  induction segs as [|s rest IH]; intros vt a n seg H; [discriminate|].
  cbn [find_segment app] in *.
  match goal with |- (if ?c then _ else _) = _ => destruct c end;
    [exact H | exact (IH vt a n seg H)].
Qed.

Lemma memory_read_app : forall segs vt (a : word) n bs,
  memory_read segs a n = Some bs -> memory_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold memory_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma code_read_app : forall segs vt (a : word) n bs,
  code_read segs a n = Some bs -> code_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma code_read_wx_app : forall segs vt (a : word) n bs,
  code_read_wx segs a n = Some bs -> code_read_wx (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read_wx in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma fetch_word_app : forall segs vt (pc : word) w,
  fetch_word segs pc = Some w -> fetch_word (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  destruct (code_read segs pc 4) as [bs|] eqn:Hc; [|discriminate].
  rewrite (code_read_app segs vt pc 4 bs Hc). exact H.
Qed.

Lemma fetch_word_wx_app : forall segs vt (pc : word) w,
  fetch_word_wx segs pc = Some w -> fetch_word_wx (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word_wx in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  destruct (code_read_wx segs pc 4) as [bs|] eqn:Hc; [|discriminate].
  rewrite (code_read_wx_app segs vt pc 4 bs Hc). exact H.
Qed.

Lemma wview_app : forall segs vt m (a : word) b,
  wview segs m a = Some b -> wview (segs ++ vt) m a = Some b.
Proof.
  intros segs vt m a b H. unfold wview in *.
  destruct (m a) as [b'|]; [exact H|].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma store_ok_app : forall segs vt m n (a : word),
  store_ok segs m a n = true -> store_ok (segs ++ vt) m a n = true.
Proof.
  intros segs vt m n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hw; [|discriminate].
  rewrite (wview_app segs vt m a b Hw). exact (IH _ H).
Qed.

(* ===================================================================== *)
(* The tree's readers, all of which funnel through the four above         *)
(* ===================================================================== *)

Lemma rom_of_app : forall segs vt (a : word) b,
  St.rom_of segs a = Some b -> St.rom_of (segs ++ vt) a = Some b.
Proof.
  intros segs vt a b H. unfold St.rom_of in *.
  destruct (memory_read segs a 1) as [bs|] eqn:Hm; [|discriminate].
  rewrite (memory_read_app segs vt a 1 bs Hm). exact H.
Qed.

Lemma img_byte_app : forall segs vt a b,
  St.img_byte segs a = Some b -> St.img_byte (segs ++ vt) a = Some b.
Proof. intros segs vt a b H. unfold St.img_byte in *. exact (rom_of_app segs vt _ b H). Qed.

Lemma rb_app : forall segs vt m a b,
  St.rb segs m a = Some b -> St.rb (segs ++ vt) m a = Some b.
Proof.
  intros segs vt m a b H. unfold St.rb in *.
  destruct (m (Z_to_bv 64 a)) as [b'|]; [exact H|].
  exact (rom_of_app segs vt _ b H).
Qed.

Lemma wb_app : forall segs vt m a,
  St.wb segs m a = true -> St.wb (segs ++ vt) m a = true.
Proof.
  intros segs vt m a H. unfold St.wb in *.
  destruct (wview segs m (Z_to_bv 64 a)) as [b|] eqn:Hw; [|discriminate].
  rewrite (wview_app segs vt m _ b Hw). reflexivity.
Qed.

Lemma img_bytes_app : forall segs vt n a bs,
  Mem.img_bytes segs a n = Some bs -> Mem.img_bytes (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt n. induction n as [|n IH]; intros a bs H; cbn [Mem.img_bytes] in *;
    [exact H|].
  destruct (memory_read segs (Z_to_bv 64 a) 1) as [l|] eqn:Hm; [|discriminate].
  destruct l as [|b l']; [discriminate|].
  rewrite (memory_read_app segs vt _ 1 _ Hm).
  destruct (Mem.img_bytes segs (a + 1) n) as [bs'|] eqn:Hi; [|discriminate].
  rewrite (IH (a + 1) bs' Hi). exact H.
Qed.

Lemma abs_readable_app : forall segs vt a n,
  Mem.abs_readable segs a n = true -> Mem.abs_readable (segs ++ vt) a n = true.
Proof.
  intros segs vt a n H. unfold Mem.abs_readable in *.
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb].
  destruct (Mem.img_bytes segs a (Z.to_nat n)) as [bs|] eqn:Hb; [|discriminate H2].
  rewrite (img_bytes_app segs vt _ a bs Hb). reflexivity.
Qed.

Lemma abs_writable_bytes_app : forall segs vt n a,
  Mem.abs_writable_bytes segs a n = true ->
  Mem.abs_writable_bytes (segs ++ vt) a n = true.
Proof.
  intros segs vt n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [Mem.abs_writable_bytes] in *. apply andb_prop in H as [H1 H2].
  destruct (find_segment segs a 1) as [seg|] eqn:Hf; [|discriminate H1].
  rewrite (find_segment_app segs vt a 1 seg Hf), H1. cbn [andb].
  exact (IH (a + 1) H2).
Qed.

Lemma abs_writable_app : forall segs vt a n,
  Mem.abs_writable segs a n = true -> Mem.abs_writable (segs ++ vt) a n = true.
Proof.
  intros segs vt a n H. unfold Mem.abs_writable in *.
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb].
  exact (abs_writable_bytes_app segs vt (Z.to_nat n) a H2).
Qed.

Lemma range_in_image_app : forall segs vt lo n,
  DrvTop.range_in_image segs lo n = true ->
  DrvTop.range_in_image (segs ++ vt) lo n = true.
Proof.
  intros segs vt lo n H. unfold DrvTop.range_in_image in *.
  apply forallb_forall. intros i Hi.
  pose proof (proj1 (forallb_forall _ _) H i Hi) as Q. cbn beta in Q.
  destruct (St.img_byte segs (lo + Z.of_nat i)) as [b|] eqn:Hb; [|discriminate Q].
  rewrite (img_byte_app segs vt _ b Hb). reflexivity.
Qed.

Lemma range_zero_app : forall segs vt lo n,
  DrvTop.range_zero segs lo n = true -> DrvTop.range_zero (segs ++ vt) lo n = true.
Proof.
  intros segs vt lo n H. unfold DrvTop.range_zero in *.
  apply forallb_forall. intros i Hi.
  pose proof (proj1 (forallb_forall _ _) H i Hi) as Q. cbn beta in Q.
  destruct (St.img_byte segs (lo + Z.of_nat i)) as [b|] eqn:Hb; [|discriminate Q].
  rewrite (img_byte_app segs vt _ b Hb). exact Q.
Qed.

Lemma ecall_atb_app : forall segs vt pc,
  DrvLib.ecall_atb segs pc = true -> DrvLib.ecall_atb (segs ++ vt) pc = true.
Proof.
  intros segs vt pc H. unfold DrvLib.ecall_atb in *.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:Hw; [|discriminate].
  rewrite (fetch_word_app segs vt _ w Hw). exact H.
Qed.

Lemma ecall_at_app : forall segs vt pc,
  PlanS.ecall_at segs pc -> PlanS.ecall_at (segs ++ vt) pc.
Proof.
  intros segs vt pc (w & Hw & He). exists w.
  split; [exact (fetch_word_app segs vt _ w Hw) | exact He].
Qed.

(* ===================================================================== *)
(* The same, phrased at [run_segments] — the form the harness uses        *)
(* ===================================================================== *)

Section AtRun.
Variable segs : list Segment.
Variable inp : ProcInput.
Variables sp mbase : word.

#[local] Notation VT := (vdso_segments (in_kernel inp) sp mbase).

Lemma find_segment_run : forall a n seg,
  find_segment segs a n = Some seg ->
  find_segment (run_segments segs inp sp mbase) a n = Some seg.
Proof. intros a n seg H. rewrite run_segments_eq. exact (find_segment_app segs VT a n seg H). Qed.

Lemma memory_read_run : forall (a : word) n bs,
  memory_read segs a n = Some bs ->
  memory_read (run_segments segs inp sp mbase) a n = Some bs.
Proof. intros a n bs H. rewrite run_segments_eq. exact (memory_read_app segs VT a n bs H). Qed.

Lemma fetch_word_run : forall (pc : word) w,
  fetch_word segs pc = Some w ->
  fetch_word (run_segments segs inp sp mbase) pc = Some w.
Proof. intros pc w H. rewrite run_segments_eq. exact (fetch_word_app segs VT pc w H). Qed.

Lemma img_byte_run : forall a b,
  St.img_byte segs a = Some b ->
  St.img_byte (run_segments segs inp sp mbase) a = Some b.
Proof. intros a b H. rewrite run_segments_eq. exact (img_byte_app segs VT a b H). Qed.

Lemma rb_run : forall m a b,
  St.rb segs m a = Some b -> St.rb (run_segments segs inp sp mbase) m a = Some b.
Proof. intros m a b H. rewrite run_segments_eq. exact (rb_app segs VT m a b H). Qed.

Lemma abs_writable_run : forall a n,
  Mem.abs_writable segs a n = true ->
  Mem.abs_writable (run_segments segs inp sp mbase) a n = true.
Proof. intros a n H. rewrite run_segments_eq. exact (abs_writable_app segs VT a n H). Qed.

Lemma range_in_image_run : forall lo n,
  DrvTop.range_in_image segs lo n = true ->
  DrvTop.range_in_image (run_segments segs inp sp mbase) lo n = true.
Proof. intros lo n H. rewrite run_segments_eq. exact (range_in_image_app segs VT lo n H). Qed.

Lemma range_zero_run : forall lo n,
  DrvTop.range_zero segs lo n = true ->
  DrvTop.range_zero (run_segments segs inp sp mbase) lo n = true.
Proof. intros lo n H. rewrite run_segments_eq. exact (range_zero_app segs VT lo n H). Qed.

Lemma ecall_atb_run : forall pc,
  DrvLib.ecall_atb segs pc = true ->
  DrvLib.ecall_atb (run_segments segs inp sp mbase) pc = true.
Proof. intros pc H. rewrite run_segments_eq. exact (ecall_atb_app segs VT pc H). Qed.

Lemma ecall_at_run : forall pc,
  PlanS.ecall_at segs pc -> PlanS.ecall_at (run_segments segs inp sp mbase) pc.
Proof. intros pc H. rewrite run_segments_eq. exact (ecall_at_app segs VT pc H). Qed.

End AtRun.

(* ===================================================================== *)
(* The one direction that does NOT transport: ABSENCE                    *)
(*                                                                       *)
(* [St.region_ok]'s [ro_valid] asks for [find_segment segs a 1 = None] —  *)
(* an address the image does NOT map.  Appending the vDSO pair can        *)
(* falsify that, so it is proved from the pair's PLACEMENT rather than    *)
(* carried: the pair sits just below                                      *)
(*   min (mbase) (page_round_down (sp - stack_max_size))                  *)
(* (LPS 75d69e00 theories/LinuxProcessSem/Run.v:290-300), and both        *)
(* [valid_mmap_base]'s floor ([State.mmap_base_min] = 0x154555557000) and *)
(* [valid_sp]'s floor ([State.sp_window_lo] = 0x7fff80000000, less the    *)
(* 8 MiB [State.stack_max_size]) are far above 2^40.  The pair is at most *)
(* 20 pages wide ([State.vdso_len_bounds]).  So every address below 2^40  *)
(* — the harness's image, heap and stage windows all live under 0x1000000 *)
(* — misses the pair outright.                                           *)
(* ===================================================================== *)

Lemma find_segment_app_none : forall segs vt a n,
  find_segment segs a n = None -> find_segment vt a n = None ->
  find_segment (segs ++ vt) a n = None.
Proof.
  induction segs as [|s rest IH]; intros vt a n H1 H2; [exact H2|].
  cbn [find_segment app] in *.
  match goal with |- (if ?c then _ else _) = _ => destruct c end;
    [discriminate H1 | exact (IH vt a n H1 H2)].
Qed.

Lemma page_round_down_Z_lower : forall n, 0 <= n -> n - page_size < page_round_down_Z n.
Proof.
  intros n Hn. unfold page_round_down_Z, page_size.
  pose proof (Z.mod_pos_bound n 4096 ltac:(lia)) as [H1 H2].
  pose proof (Z.div_mod n 4096 ltac:(lia)) as H. lia.
Qed.

Local Transparent vdso_segments.

(* Any width: the test [Z.leb seg_base a] already fails on [a < 2^40],
   whatever [n] is. *)
Lemma vdso_segments_above : forall kb sp mbase a n,
  valid_sp sp -> valid_mmap_base mbase -> a < 2 ^ 40 ->
  find_segment (vdso_segments kb sp mbase) a n = None.
Proof.
  (* Shaped after the model's own [no_ro_exec_vdso] (75d69e00
     Examples/rwx_flag_ns/rwx_flag_ns_defs.v): [unfold] + [cbv zeta], then
     DESTRUCT the emptiness test rather than [replace] it, and destruct each
     [Z.leb] rather than naming the expanded bound.  Nothing here has to match
     the let-expansion syntactically. *)
  intros kb sp mbase a n (Hs1 & Hs2 & _) (Hm1 & Hm2 & _) Ha1.
  unfold sp_window_lo, sp_window_hi in Hs1, Hs2.
  unfold mmap_base_min in Hm1.
  pose proof (vdso_len_bounds kb) as [HL1 HL2].
  pose proof (vdso_text_pages_pos kb) as HT1.
  pose proof (vdso_text_pages_le kb) as HT2.
  assert (Hsub : 0 <= bv_unsigned sp - stack_max_size)
    by (unfold stack_max_size, page_size in *; lia).
  pose proof (page_round_down_Z_lower _ Hsub) as P1.
  assert (Hmpos : 0 <= Z.min (bv_unsigned mbase)
                    (page_round_down_Z (bv_unsigned sp - stack_max_size)))
    by (unfold stack_max_size, page_size in *; lia).
  pose proof (page_round_down_Z_lower _ Hmpos) as P2.
  (* The pair's low edge.  At LPS b84e73ef the pair's top is the model's own
     [Run.vdso_pair_top] and the text's base its [Run.vdso_text_base], so the
     bounds are stated over those two and the lia steps below unfold them. *)
  assert (HPT : 2 ^ 40 + 4 * page_size + vdso_len kb <= vdso_pair_top sp mbase)
    by (unfold vdso_pair_top, stack_max_size, page_size in *; lia).
  assert (HTB : bv_unsigned (vdso_text_base kb sp mbase)
                = vdso_pair_top sp mbase - vdso_text_pages kb * page_size).
  { unfold vdso_text_base. apply bv_unsigned_Z_to_bv_u64.
    (* the top is at most sp - stack_max_size, below 2^47 (Hs2), and at least 2^40 (HPT) *)
    pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase) (page_round_down_Z (bv_unsigned sp - stack_max_size)))) as PU.
    pose proof (page_round_down_Z_le (bv_unsigned sp - stack_max_size)) as PU2.
    unfold vdso_pair_top, vdso_len, vdso_vvar_pages, stack_max_size, page_size, two_pow_64 in *. lia. }
  unfold vdso_segments. cbv zeta.
  match goal with |- find_segment (if ?c then _ else _) _ _ = _ => destruct c eqn:Hc end.
  - reflexivity.
  - apply Z.ltb_ge in Hc.
    cbn [find_segment seg_base seg_size].
    rewrite HTB. rewrite !Z2N.id by (unfold vdso_len, vdso_vvar_pages, page_size in *; lia).
    (* Both segments of the vDSO pair, and their LOW-EDGE tests only: the
       high-edge conjunct is [a + n <=? …], whose right operand is not [a], so
       the pattern below cannot catch it.  [destruct (Z.leb _ a)] with a
       WILDCARD does not work here — it elaborates a fresh evar rather than
       matching the goal, and such destructs land (measured: three of them) on a
       literal [false] (`E3, E2, E1 : false = false`) while the
       real test stays in the goal.  Match the goal. *)
    repeat (match goal with
            | |- context [ (?x <=? a)%Z ] =>
                let E := fresh "EL" in
                destruct (Z.leb_spec x a) as [E|E];
                [ exfalso; unfold vdso_len, vdso_vvar_pages, page_size in *; lia | ]
            end; cbn [andb]).
    reflexivity.
Qed.

Local Opaque vdso_segments.

Lemma find_segment_run_none : forall segs inp sp mbase a n,
  valid_sp sp -> valid_mmap_base mbase -> a < 2 ^ 40 ->
  find_segment segs a n = None ->
  find_segment (run_segments segs inp sp mbase) a n = None.
Proof.
  intros segs inp sp mbase a n Hsp Hmb Ha1 H.
  rewrite run_segments_eq. apply find_segment_app_none; [exact H|].
  exact (vdso_segments_above (in_kernel inp) sp mbase a n Hsp Hmb Ha1).
Qed.

(* ===================================================================== *)
(* EQUALITY below 2^40 — what the certificate machinery actually needs    *)
(*                                                                       *)
(* One-directional transport is NOT enough for the driver checks.         *)
(* [Mem.region_load1] feeds the background value to [Mem.assemble] as its *)
(* [base] argument, and [assemble (Some b) …] and [assemble None …] run   *)
(* DIFFERENT computations (the [None] case tiles and the [Some] case does *)
(* not, lib/FX/Mem.v:203-224).  So a background that was [None] over the  *)
(* image's list and becomes [Some] over the run's list can change the     *)
(* loaded value rather than merely create one, and [region_load] is not   *)
(* monotone.  Below 2^40 the two lists are indistinguishable to every     *)
(* reader, so the honest statement is an EQUALITY, and that is what       *)
(* carries [drv_chk] across.                                             *)
(* ===================================================================== *)

Lemma find_segment_eq_below : forall segs inp sp mbase a n,
  valid_sp sp -> valid_mmap_base mbase -> a < 2 ^ 40 ->
  find_segment (run_segments segs inp sp mbase) a n = find_segment segs a n.
Proof.
  intros segs inp sp mbase a n Hsp Hmb Ha.
  destruct (find_segment segs a n) as [seg|] eqn:Hf.
  - exact (find_segment_run segs inp sp mbase a n seg Hf).
  - exact (find_segment_run_none segs inp sp mbase a n Hsp Hmb Ha Hf).
Qed.

Lemma memory_read_eq_below : forall segs inp sp mbase (a : word) n,
  valid_sp sp -> valid_mmap_base mbase -> bv_unsigned a < 2 ^ 40 ->
  memory_read (run_segments segs inp sp mbase) a n = memory_read segs a n.
Proof.
  intros segs inp sp mbase a n Hsp Hmb Ha. unfold memory_read.
  rewrite (find_segment_eq_below segs inp sp mbase (bv_unsigned a) (Z.of_N n) Hsp Hmb Ha).
  reflexivity.
Qed.

Lemma img_bytes_eq_below : forall segs inp sp mbase n a,
  valid_sp sp -> valid_mmap_base mbase -> 0 <= a -> a + Z.of_nat n <= 2 ^ 40 ->
  Mem.img_bytes (run_segments segs inp sp mbase) a n = Mem.img_bytes segs a n.
Proof.
  intros segs inp sp mbase n. induction n as [|n IH]; intros a Hsp Hmb Ha0 Ha1;
    cbn [Mem.img_bytes]; [reflexivity|].
  assert (Hlt : bv_unsigned (Z_to_bv 64 a) < 2 ^ 40).
  { rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). lia. }
  rewrite (memory_read_eq_below segs inp sp mbase (Z_to_bv 64 a) 1 Hsp Hmb Hlt).
  destruct (memory_read segs (Z_to_bv 64 a) 1) as [l|]; [|reflexivity].
  destruct l as [|b l']; [reflexivity|].
  rewrite (IH (a + 1) Hsp Hmb ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma abs_readable_eq_below : forall segs inp sp mbase a n,
  valid_sp sp -> valid_mmap_base mbase -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 40 ->
  Mem.abs_readable (run_segments segs inp sp mbase) a n = Mem.abs_readable segs a n.
Proof.
  intros segs inp sp mbase a n Hsp Hmb Ha0 Hn Ha1. unfold Mem.abs_readable.
  rewrite (img_bytes_eq_below segs inp sp mbase (Z.to_nat n) a Hsp Hmb Ha0
             ltac:(rewrite Z2Nat.id; lia)).
  reflexivity.
Qed.

Lemma abs_writable_bytes_eq_below : forall segs inp sp mbase n a,
  valid_sp sp -> valid_mmap_base mbase -> 0 <= a -> a + Z.of_nat n <= 2 ^ 40 ->
  Mem.abs_writable_bytes (run_segments segs inp sp mbase) a n
  = Mem.abs_writable_bytes segs a n.
Proof.
  intros segs inp sp mbase n. induction n as [|n IH]; intros a Hsp Hmb Ha0 Ha1;
    cbn [Mem.abs_writable_bytes]; [reflexivity|].
  rewrite (find_segment_eq_below segs inp sp mbase a 1 Hsp Hmb ltac:(lia)).
  rewrite (IH (a + 1) Hsp Hmb ltac:(lia) ltac:(lia)). reflexivity.
Qed.

Lemma abs_writable_eq_below : forall segs inp sp mbase a n,
  valid_sp sp -> valid_mmap_base mbase -> 0 <= a -> 0 <= n -> a + n <= 2 ^ 40 ->
  Mem.abs_writable (run_segments segs inp sp mbase) a n = Mem.abs_writable segs a n.
Proof.
  intros segs inp sp mbase a n Hsp Hmb Ha0 Hn Ha1. unfold Mem.abs_writable.
  rewrite (abs_writable_bytes_eq_below segs inp sp mbase (Z.to_nat n) a Hsp Hmb Ha0
             ltac:(rewrite Z2Nat.id; lia)).
  reflexivity.
Qed.

Lemma bg_value_eq_below : forall segs inp sp mbase k r o w,
  valid_sp sp -> valid_mmap_base mbase ->
  0 <= to_Z o -> to_Z o + to_Z w <= 2 ^ 40 ->
  Mem.bg_value (run_segments segs inp sp mbase) k r o w = Mem.bg_value segs k r o w.
Proof.
  intros segs inp sp mbase k r o w Hsp Hmb Ho0 Ho1. unfold Mem.bg_value.
  destruct (Mem.rg_bg r); try reflexivity.
  destruct (PrimInt63.ltb o W64.bit62i); [|reflexivity].
  pose proof (Uint63.to_Z_bounded w) as [Hw0 _].
  rewrite (img_bytes_eq_below segs inp sp mbase (Z.to_nat (to_Z w)) (to_Z o) Hsp Hmb Ho0
             ltac:(rewrite Z2Nat.id; lia)).
  reflexivity.
Qed.

Lemma region_load1_eq_below : forall segs inp sp mbase k r o w sx,
  valid_sp sp -> valid_mmap_base mbase ->
  0 <= to_Z o -> to_Z o + to_Z w <= 2 ^ 40 ->
  Mem.region_load1 (run_segments segs inp sp mbase) k r o w sx
  = Mem.region_load1 segs k r o w sx.
Proof.
  intros segs inp sp mbase k r o w sx Hsp Hmb Ho0 Ho1. unfold Mem.region_load1.
  (* [bg_value] sits under the [let '(dirty, s) := … in] pattern match;
     destructing the lookup first keeps the rewrite out from under it. *)
  destruct (IMap.find (Mem.granule o) (Mem.rg_cells r)) as [[d s]|];
    rewrite (bg_value_eq_below segs inp sp mbase k r o w Hsp Hmb Ho0 Ho1);
    reflexivity.
Qed.

(* [Step.can_read] / [Step.can_write] (lib/FX/Step.v:914,934) sit OUTSIDE
   [Step]'s [Section WithSegs], so they take [segs] explicitly.  [segs]
   reaches them only at [k = 0], through [abs_readable] / [abs_writable]. *)

Lemma can_read_eq_below : forall segs inp sp mbase fs priv k r key w,
  valid_sp sp -> valid_mmap_base mbase -> to_Z key + to_Z w <= 2 ^ 40 ->
  Step.can_read (run_segments segs inp sp mbase) fs priv k r key w
  = Step.can_read segs fs priv k r key w.
Proof.
  intros segs inp sp mbase fs priv k r key w Hsp Hmb Hkw. unfold Step.can_read.
  destruct (PrimInt63.eqb k 0%uint63); [|reflexivity].
  pose proof (Uint63.to_Z_bounded key) as [Hk0 _].
  pose proof (Uint63.to_Z_bounded w) as [Hw0 _].
  rewrite (abs_readable_eq_below segs inp sp mbase (to_Z key) (to_Z w)
             Hsp Hmb Hk0 Hw0 Hkw).
  reflexivity.
Qed.

Lemma can_write_eq_below : forall segs inp sp mbase fs priv k r key w,
  valid_sp sp -> valid_mmap_base mbase -> to_Z key + to_Z w <= 2 ^ 40 ->
  Step.can_write (run_segments segs inp sp mbase) fs priv k r key w
  = Step.can_write segs fs priv k r key w.
Proof.
  intros segs inp sp mbase fs priv k r key w Hsp Hmb Hkw. unfold Step.can_write.
  destruct (PrimInt63.eqb k 0%uint63).
  - pose proof (Uint63.to_Z_bounded key) as [Hk0 _].
    pose proof (Uint63.to_Z_bounded w) as [Hw0 _].
    rewrite (abs_writable_eq_below segs inp sp mbase (to_Z key) (to_Z w)
               Hsp Hmb Hk0 Hw0 Hkw).
    reflexivity.
  - rewrite (can_read_eq_below segs inp sp mbase fs priv k r key w Hsp Hmb Hkw).
    reflexivity.
Qed.

(* ===================================================================== *)
(* THE REMAINING STEP, and the hypothesis that dissolves it              *)
(*                                                                       *)
(* [Mem.region_load] (lib/FX/Mem.v:281-289) splits a cross-granule access *)
(* into [region_load1 k r o w1] and [region_load1 k r (o + w1) w2] with   *)
(*   w1 = PrimInt63.sub 8 (Mem.gidx o),  w2 = PrimInt63.sub w w1,         *)
(* all in [PrimInt63].  Carrying the bound of [region_load1_eq_below]     *)
(* through that split under the hypothesis [to_Z o + to_Z w <= 2^40] does *)
(* NOT work: in the [else] branch [in_granule o w = false] gives only     *)
(* [to_Z (gidx o) + to_Z w > 8], so with [gidx o = 7], [w = 2] one gets   *)
(* [w1 = 1] and nothing bounds [to_Z o + 8].                              *)
(*                                                                       *)
(* The cure is to state the bound on the GRANULE rather than on the       *)
(* access, which is sound because every width reaching [region_load] is   *)
(* at most 8 ([Mem.wok_b] / [DrvRoot.wokb] accept only 1, 2, 4, 8):       *)
(*                                                                       *)
(*   0 <= to_Z o -> to_Z w <= 8 -> to_Z o + 8 <= 2^40                     *)
(*                                                                       *)
(* Under it both sub-accesses are immediate:                              *)
(*   - [Mem.gidx o = PrimInt63.land o 7], so [to_Z (gidx o) <= 7] and     *)
(*     [to_Z w1 = 8 - to_Z (gidx o)] in [1..8] with no wrap, giving       *)
(*     [to_Z o + to_Z w1 <= to_Z o + 8 <= 2^40];                          *)
(*   - [to_Z o + 8 <= 2^40 < 2^63] so [PrimInt63.add o w1] does not wrap   *)
(*     ([Uint63.add_spec]) and [to_Z (o + w1) = to_Z o + to_Z w1]; with    *)
(*     [w1 <= w] (the [else] branch) [Uint63.sub_spec] gives              *)
(*     [to_Z w2 = to_Z w - to_Z w1], so the second access also ends at    *)
(*     [to_Z o + to_Z w <= to_Z o + 8 <= 2^40].                           *)
(*                                                                       *)
(* [can_read]/[can_write] (lib/FX/Step.v:914,934) take the same bound and *)
(* are easier: [segs] enters only at [k = 0], through                     *)
(* [abs_readable_eq_below] / [abs_writable_eq_below] above.                *)
(*                                                                       *)
(* From there: [do_load_eq_below] and [do_store_eq_below]                 *)
(* (lib/FX/Step.v:1066,1106) -> [remat1_eq_below] -> [remat_eq_below]     *)
(* -> [drv_of_main_eq_below] (lib/Glue/DrvRoot.v:20-62) ->                *)
(* [drv_chk_eq_below] (lib/Glue/DrvTop.v:301), whose four remaining       *)
(* checks ([sstate_wfb], [entails], [cells_public_b], [apart_chk],        *)
(* [no_heap_ops]) do not mention [segs] at all.                           *)
(*                                                                       *)
(* At each [drv_chk] call site the side condition is decidable over the   *)
(* closed rematerialisation list:                                         *)
(*   forallb (fun aw => to_Z (fst aw) + 8 <=? 2^40) rm = true             *)
(* by [vm_compute].  And in [remat1] the address is [VL (wlit (fst aw))], *)
(* so [addr_of] gives [k = 0] and [can_read] already forces the range     *)
(* into the image — the bound can be derived there rather than assumed.   *)
(* ===================================================================== *)

End RunSeg.
