(** * reac-pw/fuzz_link (asan, image A): T0.6 for the memory-FILE clauses of AMemFile.v, on link's asan image.

    The A twin of lib/MemFileT06.v (plain). [link_amf_t06] is a satisfiability lemma. It states, at link's asan
    image (pin 059dae63e07c, [tfibsegs]), at every allocation ceiling the run may have (the [RunCeil] of the
    section, so link's own) and at link's start state (the image's bytes):
    1. the record, the list head and the layout are read from link's asan code ([link_amf_code_ok],
       AMemFile.v), and the record's head is the A frame's ([link_amf_head_law]);
    2. at the start state the GI conjunct holds in its "nothing kept" arm and the three stdio words are 0, from
       the image's bytes alone (so the clause [amf_sink] holds before the first mark);
    3. the one-FILE arm and the post's clause [amf_sink] hold of every FILE state in the ranges the code can leave
       (flags F_NORD or F_NORD | F_ERR, orientation 0 or -1, the window empty or active with at most 1024 bytes
       pending, [pos <= len <= size]): for EVERY block the A allocator may hold for fmemopen's 1304 bytes (what
       the AR laws give a live block of the ledger: 16-aligned, at or above 4096, below the ceiling, not an image
       byte; AMemFile.v [amf_block_facts]), the memory the modeled stores give ([amf_state]: fmemopen,
       __ofl_add, mark_quietly, reac_served_say_to, then the changing words) satisfies both; and such a block
       exists under every ceiling, in the application range, so the arm is not vacuous. That the run's memory IS
       such a state is what the walks of fmemopen, rewind, vfprintf and mwrite prove, against [amemfile_at];
    4. the exit path: close_file's instructions ([__stdio_exit]'s list loop, asan 0x969b0-0x96a08, in
       [link_amf_code]) branch on [lock], [wpos] / [wbase], [rpos] / [rend] and [next], and on that FILE
       [amemfile_at] fixes [lock] = -1, [write] = mwrite, [rpos] = [rend] = 0 and [next] = 0; __ofl_lock's
       __lock returns at once when [__libc.need_locks] is 0 ([amf_env]; 0x9b4d8 / 0x9b4dc in [link_amf_code]);
       mwrite has no [ecall] and transfers control only to itself, ___errno_location and the memcpy
       interceptor's entry 0x52d74 (= [pc_wrap_memcpy Tfib_code], whose behaviour is the AsanAPI's
       [aa_memcpy_icpt]), or back to its caller; ___errno_location calls nothing ([link_amwrite_closure_ok]);
       mwrite's own stores are exactly [link_amwrite_stores] (its stack frame, the FILE's words, the cookie's
       [pos] / [len], errno when a write passes the cookie's size, a NUL at [buf + len] when [len < size]).
       That the interceptor's stores land in [g_said] ([len <= size - pos] bytes at [buf + pos], both ranges
       addressable: the kept block's bytes and the global's) is an obligation of the mwrite walk, not a fact
       checked here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP02 YI04 YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AMemFile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(** ** Control-flow scan (the plain MemFileT06.v's, over the asan table)

    [ctrl_ok lo hi calls pc i]: [i] at [pc] is not ecall / ebreak / CSR / atomic / fence.i; a jump or branch
    stays in [lo, hi); a call ([jal ra]) goes to an entry in [calls]; the only indirect jump is [ret]. *)
Definition ctrl_ok (lo hi : Z) (calls : list Z) (pc : Z) (i : instr) : bool :=
  match i with
  | Jal rd off =>
      let t := pc + bv_signed off in
      if Z.eqb (bv_unsigned rd) 0 then (lo <=? t) && (t <? hi)
      else Z.eqb (bv_unsigned rd) 1 && existsb (Z.eqb t) calls
  | Jalr rd rs off => Z.eqb (bv_unsigned rd) 0 && Z.eqb (bv_unsigned rs) 1 && Z.eqb (bv_unsigned off) 0
  | Branch _ _ _ off => let t := pc + bv_signed off in (lo <=? t) && (t <? hi)
  | Ecall | Ebreak | Csr _ _ _ _ | CsrI _ _ _ _ | Lr _ _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _
  | FenceI _ _ _ => false
  | _ => true
  end.

Fixpoint scan_ok (tbl : ctable) (lo hi : Z) (calls : list Z) (pc : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match code_at tbl pc with
      | Some i => ctrl_ok lo hi calls pc i && scan_ok tbl lo hi calls (pc + 4) n'
      | None => false
      end
  end.

Lemma scan_sound : forall tbl lo hi calls n pc, scan_ok tbl lo hi calls pc n = true ->
  forall k, (k < n)%nat ->
  exists i, code_at tbl (pc + 4 * Z.of_nat k) = Some i /\ ctrl_ok lo hi calls (pc + 4 * Z.of_nat k) i = true.
Proof.
  intros tbl lo hi calls n. induction n as [|n IH]; intros pc H k Hk; [lia|].
  cbn [scan_ok] in H. destruct (code_at tbl pc) as [i|] eqn:E; [|discriminate].
  apply andb_prop in H as [Hc H]. destruct k as [|k].
  - exists i. replace (pc + 4 * Z.of_nat 0) with pc by lia. split; [exact E | exact Hc].
  - destruct (IH (pc + 4) H k ltac:(lia)) as (i' & E' & Hc'). exists i'.
    replace (pc + 4 * Z.of_nat (S k)) with (pc + 4 + 4 * Z.of_nat k) by lia. split; [exact E' | exact Hc'].
Qed.

(** Every instruction a scanned range holds is fetched from the asan image, is not [ecall], and decodes. *)
Lemma scan_fetch : forall tbl lo hi calls n pc, table_ok tfibsegs tbl -> scan_ok tbl lo hi calls pc n = true ->
  forall k, (k < n)%nat -> exists w i,
    fetch_word tfibsegs (Z_to_bv 64 (pc + 4 * Z.of_nat k)) = Some w /\ is_ecall w = false /\
    decode_any w = Some (i, 4) /\ ctrl_ok lo hi calls (pc + 4 * Z.of_nat k) i = true.
Proof.
  intros tbl lo hi calls n pc Ht H k Hk. destruct (scan_sound tbl lo hi calls n pc H k Hk) as (i & E & Hc).
  destruct (code_at_sound tfibsegs tbl _ i Ht E) as (w & Hf & He & Hd). exists w, i. auto.
Qed.

(** mwrite (asan 0x96cc0, 276 bytes) and ___errno_location (0x90a7c, 12 bytes): mwrite calls itself,
    ___errno_location and the memcpy interceptor's entry 0x52d74 only; ___errno_location calls nothing. *)
Definition link_amwrite_closure : bool :=
  scan_ok amf_tbl 0x96cc0 (0x96cc0 + 276) [0x96cc0; 0x90a7c; 0x52d74] 0x96cc0 69 &&
  scan_ok amf_tbl 0x90a7c (0x90a7c + 12) [] 0x90a7c 3.

Lemma link_amwrite_closure_ok : link_amwrite_closure = true.
Proof. vm_compute. reflexivity. Qed.

(** The memcpy mwrite calls is the API's interceptor entry. *)
Lemma link_amwrite_memcpy : pc_wrap_memcpy Tfib_code = 0x52d74.
Proof. reflexivity. Qed.

(** mwrite's stores, all of them: [link_amwrite_has_only] checks that no other instruction of mwrite is a
    store (s2 is the FILE argument, s4 = f->cookie from +0x2c [ld s4,0x98(s2)]). *)
Definition link_amwrite_stores : list (Z * ishape) := [
  (0x96cc4, SSt 8 2 1 0x28); (0x96cc8, SSt 8 2 8 0x20); (0x96ccc, SSt 8 2 9 0x18);
  (0x96cd0, SSt 8 2 18 0x10); (0x96cd4, SSt 8 2 19 8); (0x96cd8, SSt 8 2 20 0);  (* its stack frame *)
  (0x96cec, SLd 8 true 20 18 0x98);   (* +0x2c ld s4,0x98(s2): s4 = f->cookie *)
  (0x96cfc, SSt 8 18 12 0x28);        (* +0x3c f->wpos = f->wbase (the flush) *)
  (0x96d2c, SSt 8 20 10 0);           (* +0x6c c->pos = c->len (mode 'a' only) *)
  (0x96d4c, SSt 4 10 11 0);           (* +0x8c errno = ENOSPC (a write past the size) *)
  (0x96d58, SSt 4 18 10 0);           (* +0x98 f->flags |= F_ERR (same arm) *)
  (0x96d5c, SSt 8 18 0 0x20); (0x96d60, SSt 8 18 0 0x28); (0x96d64, SSt 8 18 0 0x38);  (* wend = wpos = wbase = 0 *)
  (0x96d80, SJal 1 0x52d74);          (* +0xc0 memcpy (c->buf + c->pos, buf, len), the interceptor *)
  (0x96d90, SSt 8 20 10 0);           (* +0xd0 c->pos += len *)
  (0x96d9c, SSt 8 20 10 8);           (* +0xdc c->len = c->pos *)
  (0x96dac, SSt 1 10 0 0)             (* +0xec c->buf[c->len] = 0, when len < size *)
].

Fixpoint stores_listed (tbl : ctable) (allowed : list Z) (pc : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match code_at tbl pc with
      | Some (Store _ _ _ _) => existsb (Z.eqb pc) allowed && stores_listed tbl allowed (pc + 4) n'
      | Some (FStore _ _ _ _) | Some (Sc _ _ _ _ _ _) | Some (Amo _ _ _ _ _ _ _) => false
      | Some _ => stores_listed tbl allowed (pc + 4) n'
      | None => false
      end
  end.

Lemma link_amwrite_stores_ok : code_list_ok amf_tbl link_amwrite_stores = true.
Proof. vm_compute. reflexivity. Qed.

Lemma link_amwrite_has_only : stores_listed amf_tbl (map fst link_amwrite_stores) 0x96cc0 69 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Link's asan image: the heads and the stdio words are image bytes; a live heap block is not *)
Definition in_imgb (segs : list Segment) (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.

Lemma in_imgb_sound : forall segs a, in_imgb segs a = true -> in_img segs a.
Proof.
  intros segs a H. unfold in_imgb in H. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hin | lia].
Qed.

Lemma range_in_img : forall lo n, forallb (fun k => in_imgb tfibsegs (lo + Z.of_nat k)) (seq 0 n) = true ->
  forall a, lo <= a < lo + Z.of_nat n -> in_img tfibsegs a.
Proof.
  intros lo n H a Ha. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (a - lo)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (lo + (a - lo)) with a in H by lia. exact (in_imgb_sound _ _ H).
Qed.

Lemma link_amf_in_img : forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a -> in_img tfibsegs a.
Proof.
  intros a Ha. cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded amf_need_locks
    amf_ofl_lock link_amf] in Ha.
  destruct Ha as [[H | [H | H]] | [H | [H | H]]].
  - apply (range_in_img 0x62fec0 8); [vm_compute; reflexivity | cbn; lia].
  - apply (range_in_img 0x6312e0 8); [vm_compute; reflexivity | cbn; lia].
  - apply (range_in_img 0x652308 8); [vm_compute; reflexivity | cbn; lia].
  - apply (range_in_img 0x651ea1 1); [vm_compute; reflexivity | cbn; lia].
  - apply (range_in_img 0x651ea3 1); [vm_compute; reflexivity | cbn; lia].
  - apply (range_in_img 0x652300 4); [vm_compute; reflexivity | cbn; lia].
Qed.

(** Every image byte lies below 0x700000 (the asan image's last load segment ends at 0x6534f0). *)
Lemma link_ain_img_range : forall a, in_img tfibsegs a -> a < 0x700000.
Proof.
  intros a (sg & Hs & Ha).
  assert (H : forallb (fun sg : Segment => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? 0x700000) tfibsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H sg Hs). apply Z.leb_le in H. lia.
Qed.

Lemma link_aapart_of_img : forall f n h m, 0 < n -> 0 < m -> (forall a, h <= a < h + m -> in_img tfibsegs a) ->
  (forall i, 0 <= i < n -> ~ in_img tfibsegs (f + i)) -> amf_apart f n h m.
Proof.
  intros f n h m Hn Hm Hh Hf. unfold amf_apart.
  destruct (Z_le_gt_dec (f + n) h) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (h + m) f) as [H'|H']; [right; exact H'|].
  exfalso. apply (Hf (Z.max f h - f)); [lia|].
  replace (f + (Z.max f h - f)) with (Z.max f h) by lia. apply Hh. lia.
Qed.

Lemma link_aheads_ok : amf_heads_ok link_amf.
Proof.
  cbv [amf_heads_ok amf_apart amf_sink_addr amf_say_addr amf_size amf_ofl_head amf_threaded amf_need_locks
    amf_ofl_lock link_amf]. lia.
Qed.

(** A block the A allocator holds for the FILE is placed as [amf_place] needs. *)
Lemma link_amf_place : forall f, 0 < f -> f + AMF_BLOCK <= 2 ^ 64 -> f mod 16 = 0 ->
  (forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (f + i)) -> amf_place link_amf f.
Proof.
  intros f H0 H1 H2 Hf. unfold amf_place.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  assert (HB : 0 < AMF_BLOCK) by (unfold AMF_BLOCK; lia).
  assert (Hi : forall h m, 0 < m -> (forall a, h <= a < h + m -> amf_head_addr link_amf a \/ amf_env_addr link_amf a) ->
    amf_apart f AMF_BLOCK h m).
  { intros h m Hm Hr. apply link_aapart_of_img; [exact HB | exact Hm | | exact Hf].
    intros a Ha. exact (link_amf_in_img a (Hr a Ha)). }
  repeat split; apply Hi; try lia; intros a Ha;
    cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded amf_need_locks
      amf_ofl_lock link_amf] in *; lia.
Qed.

(** ** The start state: the image's bytes *)
Lemma link_amf_start : forall m,
  (forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
     mbyte tfibsegs m a = seg_rom tfibsegs (Z_to_bv 64 a)) ->
  amf_gi tfibsegs link_amf [] m /\ amf_env tfibsegs link_amf m.
Proof.
  intros m Hrom.
  assert (R : forall a, (amf_head_addr link_amf a \/ amf_env_addr link_amf a) ->
     forall v, seg_rom tfibsegs (Z_to_bv 64 a) = v -> mbyte tfibsegs m a = v)
    by (intros a Ha v <-; apply Hrom; exact Ha).
  cbv [amf_head_addr amf_env_addr amf_ofl_head amf_sink_addr amf_say_addr amf_threaded amf_need_locks
    amf_ofl_lock link_amf] in R.
  split.
  - left. split; [|reflexivity]. unfold amf_heads.
    cbv [amf_ofl_head amf_sink_addr amf_say_addr amf_ofl_lock link_amf].
    split; [|split]; intros k Hk;
      (do 8 (destruct k as [|k]; [apply R; [cbn; lia | vm_compute; reflexivity] |])); lia.
  - unfold amf_env. cbv [amf_threaded amf_need_locks amf_ofl_lock link_amf].
    split; [|split]; intros k Hk;
      (do 4 (destruct k as [|k]; [apply R; [cbn; lia | vm_compute; reflexivity] |])); lia.
Qed.

Section t06.
Context {rc : YM05.RunCeil}.

(** A block for the FILE exists under link's own ceiling, whatever it is, in the application range and off
    the image: what the AR laws give a live block of the A ledger. *)
Lemma link_amf_block_exists : exists f, 4096 <= f /\ f + AMF_BLOCK <= alloc_ceiling /\ f mod 16 = 0 /\
  in_app f AMF_BLOCK /\ (forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (f + i)).
Proof.
  pose proof alloc_ceiling_value as [[Hc _] _].
  exists 0x10000000. split; [lia|]. split; [unfold AMF_BLOCK; lia|]. split; [reflexivity|].
  split; [unfold in_app, AMF_BLOCK, kLowShadowBeg; lia|].
  intros i Hi Hin. apply link_ain_img_range in Hin. unfold AMF_BLOCK in Hi. lia.
Qed.

(** Every return after the first mark, for every block the A allocator may give fmemopen. *)
Lemma link_amf_returns : forall m f fl om wend wpos wbase pos len,
  4096 <= f -> f + AMF_BLOCK <= alloc_ceiling -> f mod 16 = 0 ->
  (forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (f + i)) ->
  fl = AF_NORD \/ fl = AF_NORD + AF_ERR -> om = 0 \/ om = AU32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= AMF_BUFSIZ /\ wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF + k /\ wbase = f + AMF_BUF) ->
  0 <= pos <= len -> len <= amf_size link_amf ->
  amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (amf_state link_amf m f fl om wend wpos wbase pos len) /\
  (amf_env tfibsegs link_amf m ->
   amf_sink tfibsegs link_amf (amf_state link_amf m f fl om wend wpos wbase pos len)).
Proof.
  intros m f fl om wend wpos wbase pos len Hf0 Hf1 Hf2 Hfi Hfl Hom Hw Hp Hl.
  pose proof alloc_ceiling_lt as Hc.
  assert (HP : amf_place link_amf f) by (apply link_amf_place; [lia | lia | exact Hf2 | exact Hfi]).
  split.
  - apply (amf_state_gi tfibsegs link_amf); [exact HP | exact link_aheads_ok | exact Hfl | exact Hom | exact Hw | exact Hp | exact Hl].
  - intros He. apply (amf_state_sink tfibsegs link_amf);
      [exact HP | exact link_aheads_ok | exact Hfl | exact Hom | exact Hw | exact Hp | exact Hl | exact He].
Qed.

(** The T0.6 lemma (see the head of this file for what each part says). *)
Theorem link_amf_t06 :
  code_list_ok amf_tbl link_amf_code = true /\ @amf_head_law link_asink_head link_amf /\
  (forall m,
     (forall a, amf_head_addr link_amf a \/ amf_env_addr link_amf a ->
        mbyte tfibsegs m a = seg_rom tfibsegs (Z_to_bv 64 a)) ->
     amf_gi tfibsegs link_amf [] m /\ amf_env tfibsegs link_amf m /\ amf_sink tfibsegs link_amf m) /\
  (forall m f fl om wend wpos wbase pos len,
     4096 <= f -> f + AMF_BLOCK <= alloc_ceiling -> f mod 16 = 0 ->
     (forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (f + i)) ->
     fl = AF_NORD \/ fl = AF_NORD + AF_ERR -> om = 0 \/ om = AU32M1 ->
     (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
     (exists k, 0 <= k <= AMF_BUFSIZ /\ wend = f + AMF_BUF + AMF_BUFSIZ /\ wpos = f + AMF_BUF + k /\ wbase = f + AMF_BUF) ->
     0 <= pos <= len -> len <= amf_size link_amf ->
     amf_gi tfibsegs link_amf [(f, AMF_BLOCK)] (amf_state link_amf m f fl om wend wpos wbase pos len) /\
     (amf_env tfibsegs link_amf m ->
      amf_sink tfibsegs link_amf (amf_state link_amf m f fl om wend wpos wbase pos len))) /\
  (exists f, 4096 <= f /\ f + AMF_BLOCK <= alloc_ceiling /\ f mod 16 = 0 /\ in_app f AMF_BLOCK /\
     (forall i, 0 <= i < AMF_BLOCK -> ~ in_img tfibsegs (f + i))) /\
  (forall m f, amemfile_at tfibsegs link_amf m f ->
     val_mem tfibsegs m (f + 140) 4 AU32M1 /\ val_mem tfibsegs m (f + 72) 8 (amf_write link_amf) /\
     val_mem tfibsegs m (f + 8) 8 0 /\ val_mem tfibsegs m (f + 16) 8 0 /\ val_mem tfibsegs m (f + 112) 8 0) /\
  link_amwrite_closure = true /\ pc_wrap_memcpy Tfib_code = 0x52d74 /\
  code_list_ok amf_tbl link_amwrite_stores = true /\
  stores_listed amf_tbl (map fst link_amwrite_stores) 0x96cc0 69 = true.
Proof.
  split; [exact link_amf_code_ok|].
  split; [exact link_amf_head_law|].
  split.
  { intros m Hm. destruct (link_amf_start m Hm) as [HG He].
    split; [exact HG|]. split; [exact He|]. exact (amf_sink_of_gi tfibsegs link_amf [] m HG He). }
  split; [exact link_amf_returns|].
  split; [exact link_amf_block_exists|].
  split; [intros m f H; exact (amemfile_close_reads tfibsegs link_amf m f H)|].
  split; [exact link_amwrite_closure_ok|].
  split; [exact link_amwrite_memcpy|].
  split; [exact link_amwrite_stores_ok | exact link_amwrite_has_only].
Qed.

End t06.
