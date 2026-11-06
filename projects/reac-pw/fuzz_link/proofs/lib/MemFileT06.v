(** * reac-pw/fuzz_link (plain): T0.6 for the memory-FILE clauses of MemFile.v, on link's own image.

    [link_mf_t06] is a satisfiability lemma. It states, at link's plain image, at every allocation ceiling the
    run may have (the [RunCeil] of the section, so link's own) and at link's start state (the image's bytes):
    1. the record and the layout are read from link's code ([link_mf_code_ok], MemFile.v);
    2. at the start state the GI conjunct holds in its [g_sink = 0] arm and the stdio state [closed_stdio_env]
       holds, from the image's bytes alone (the frame's [sink_none] needs both); [link_mf_gi0] gives the
       conjunct from the frame's own first-call premise [G_img];
    3. the one-FILE arm and the post's clause [mf_sink] hold of every FILE state in the ranges the code can
       leave (flags F_NORD or F_NORD | F_ERR, orientation 0 or -1, the window empty or active with at most
       1024 bytes pending, [pos <= len <= size]): for EVERY block malloc may return for fmemopen's 1304 bytes
       (non-zero, 16-aligned, fresh: what the frame malloc contract's [malloc_ret] gives), the memory the
       modeled stores give ([mf_state]: fmemopen, __ofl_add, mark_quietly, reac_served_say_to, then the
       changing words) satisfies both; and such a block exists under every ceiling, so the arm is not
       vacuous. That the run's memory IS such a state is what the walks of fmemopen, rewind, vfprintf and
       mwrite prove, against [memfile_at];
    4. the exit path: [close_file]'s instructions ([__stdio_exit]'s list loop, plain 0x19adc-0x19b34, checked
       in [link_mf_code]) branch on [lock] (+0x8c, skip __lockfile when negative), [wpos] / [wbase] (call
       f->write when they differ), [rpos] / [rend] (call f->seek when they differ) and [next] (+0x70, leave
       the loop when 0), and on that FILE [memfile_at] fixes [lock] = -1, [write] = mwrite, [rpos] = [rend]
       = 0 and [next] = 0; mwrite, with everything it calls (memcpy, ___errno_location), has no [ecall] and
       transfers control only inside those three functions or back to its caller ([link_mwrite_closure_ok]),
       so it makes no system call and writes no byte to a file descriptor; mwrite's own stores are exactly
       [link_mwrite_stores] (its stack frame, the FILE's words, the cookie's [pos] / [len], errno when a
       write passes the cookie's size, and a NUL at [buf + len] when [len < size]). That memcpy's stores
       land in [g_said] ([len <= size - pos] bytes at [buf + pos]) is an obligation of the mwrite walk,
       not a fact checked here. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YK15 YM06 YP09 YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI06 YI16 YI00 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH03 YH02 YI5b YI5c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0g YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import MemFile.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** ** Control-flow scan

    [ctrl_ok lo hi calls pc i]: [i] at [pc] is not ecall / ebreak / CSR / atomic / fence.i; a jump or branch
    stays in [lo, hi); a call ([jal ra]) goes to an entry in [calls]; the only indirect jump is [ret]
    ([jalr zero, 0(ra)]). [scan_ok] checks [n] consecutive 4-byte instructions from [pc]. *)
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

(** Every instruction a scanned range holds is fetched from the image, is not [ecall], and decodes. *)
Lemma scan_fetch : forall tbl lo hi calls n pc, table_ok src0segs tbl -> scan_ok tbl lo hi calls pc n = true ->
  forall k, (k < n)%nat -> exists w i,
    fetch_word src0segs (Z_to_bv 64 (pc + 4 * Z.of_nat k)) = Some w /\ is_ecall w = false /\
    decode_any w = Some (i, 4) /\ ctrl_ok lo hi calls (pc + 4 * Z.of_nat k) i = true.
Proof.
  intros tbl lo hi calls n pc Ht H k Hk. destruct (scan_sound tbl lo hi calls n pc H k Hk) as (i & E & Hc).
  destruct (code_at_sound src0segs tbl _ i Ht E) as (w & Hf & He & Hd). exists w, i. auto.
Qed.

(** mwrite (plain 0x19544, 276 bytes), memcpy (0x1ec5c, 1028 bytes) and ___errno_location (0x16e04, 12
    bytes): mwrite calls itself, ___errno_location and memcpy only; memcpy and ___errno_location call
    nothing. *)
Definition link_mwrite_closure : bool :=
  scan_ok src0tbl 0x19544 (0x19544 + 276) [0x19544; 0x16e04; 0x1ec5c] 0x19544 69 &&
  scan_ok src0tbl 0x1ec5c (0x1ec5c + 1028) [] 0x1ec5c 257 &&
  scan_ok src0tbl 0x16e04 (0x16e04 + 12) [] 0x16e04 3.

Lemma link_mwrite_closure_ok : link_mwrite_closure = true.
Proof. vm_compute. reflexivity. Qed.

(** mwrite's stores, all of them: [link_mwrite_has_only] checks that no other instruction of mwrite is a
    store (s2 is the FILE argument, s4 = f->cookie from +0x2c [ld s4,0x98(s2)]). *)
Definition link_mwrite_stores : list (Z * ishape) := [
  (0x19548, SSt 8 2 1 0x28); (0x1954c, SSt 8 2 8 0x20); (0x19550, SSt 8 2 9 0x18);
  (0x19554, SSt 8 2 18 0x10); (0x19558, SSt 8 2 19 8); (0x1955c, SSt 8 2 20 0);  (* its stack frame *)
  (0x19570, SLd 8 true 20 18 0x98);   (* +0x2c ld s4,0x98(s2): s4 = f->cookie *)
  (0x19580, SSt 8 18 12 0x28);        (* +0x3c f->wpos = f->wbase (the flush) *)
  (0x195b0, SSt 8 20 10 0);           (* +0x6c c->pos = c->len (mode 'a' only) *)
  (0x195d0, SSt 4 10 11 0);           (* +0x8c errno = ENOSPC (a write past the size) *)
  (0x195dc, SSt 4 18 10 0);           (* +0x98 f->flags |= F_ERR (same arm) *)
  (0x195e0, SSt 8 18 0 0x20); (0x195e4, SSt 8 18 0 0x28); (0x195e8, SSt 8 18 0 0x38);  (* wend = wpos = wbase = 0 *)
  (0x19604, SJal 1 0x1ec5c);          (* +0xc0 memcpy (c->buf + c->pos, buf, len) *)
  (0x19614, SSt 8 20 10 0);           (* +0xd0 c->pos += len *)
  (0x19620, SSt 8 20 10 8);           (* +0xdc c->len = c->pos *)
  (0x19630, SSt 1 10 0 0)            (* +0xec c->buf[c->len] = 0, when len < size *)
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

Lemma link_mwrite_stores_ok : code_list_ok src0tbl link_mwrite_stores = true.
Proof. vm_compute. reflexivity. Qed.

Lemma link_mwrite_has_only : stores_listed src0tbl (map fst link_mwrite_stores) 0x19544 69 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Link's image: where the heads and the stdio words lie *)
Lemma link_in_img_range : forall a, in_img src0_msyms a -> 0x10000 <= a < 0x97000.
Proof.
  intros a [_ (s & Hs & Ha)].
  assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) &&
    (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x97000)) (segments_reserved src0segs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma link_apart_of_img : forall f n h m, 0 < n -> 0 < m -> 0x21000 <= h -> h + m <= 0x97000 ->
  (forall i, 0 <= i < n -> ~ in_img src0_msyms (f + i)) -> mf_apart f n h m.
Proof.
  intros f n h m Hn Hm Hh0 Hh1 Hf. unfold mf_apart.
  destruct (Z_le_gt_dec (f + n) h) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (h + m) f) as [H'|H']; [right; exact H'|].
  exfalso. apply (Hf (Z.max f h - f)); [lia|].
  replace (f + (Z.max f h - f)) with (Z.max f h) by lia.
  apply src0_sink_in_img. lia.
Qed.

Lemma link_heads_ok : mf_heads_ok link_mf.
Proof.
  cbv [mf_heads_ok mf_apart mf_sink_addr mf_say_addr mf_size link_mf sk_ofl_head sk_threaded sk_ofl_lock
    src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc]. lia.
Qed.

(** A block malloc returns for the FILE is placed as [mf_place] needs. *)
Lemma link_mf_place : forall f, 0 < f -> f + MF_BLOCK <= 2 ^ 64 -> f mod 16 = 0 ->
  (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)) -> mf_place link_mf f.
Proof.
  intros f H0 H1 H2 Hf. unfold mf_place.
  split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  assert (HB : 0 < MF_BLOCK) by (unfold MF_BLOCK; lia).
  cbv [mf_sink_addr mf_say_addr link_mf sk_ofl_head sk_threaded sk_ofl_lock
    src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc].
  repeat split; apply link_apart_of_img; try lia; exact Hf.
Qed.

(** ** The start state: the image's bytes *)
Lemma link_mf_start : forall mem,
  (forall a, mf_head_addr link_mf a \/ a = @sk_threaded src0_sink \/
     (@sk_ofl_lock src0_sink <= a < @sk_ofl_lock src0_sink + 4) ->
     mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
  mf_gi src0_msyms link_mf [] mem /\ closed_stdio_env src0_msyms mem.
Proof.
  intros mem Hrom.
  assert (R : forall a, (mf_head_addr link_mf a \/ a = @sk_threaded src0_sink \/
     (@sk_ofl_lock src0_sink <= a < @sk_ofl_lock src0_sink + 4)) ->
     forall v, seg_rom src0segs (Z_to_bv 64 a) = v -> mbyte src0segs mem a = v)
    by (intros a Ha v <-; apply Hrom; exact Ha).
  cbv [mf_head_addr mf_sink_addr mf_say_addr link_mf sk_ofl_head sk_threaded sk_ofl_lock
    src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc] in R.
  split.
  - left. split; [|reflexivity]. unfold mf_heads. change (ms_segs src0_msyms) with src0segs.
    cbv [mf_sink_addr mf_say_addr link_mf sk_ofl_head src0_sink_head src0_D_ofl_head].
    split; [|split]; intros k Hk;
      (do 8 (destruct k as [|k]; [apply R; [cbn; lia | vm_compute; reflexivity] |])); lia.
  - unfold closed_stdio_env. change (ms_segs src0_msyms) with src0segs.
    cbv [sk_threaded sk_ofl_lock src0_sink src0_D_ofl_lock src0_D_libc].
    split; intros k Hk;
      (do 4 (destruct k as [|k]; [apply R; [cbn; lia | vm_compute; reflexivity] |])); lia.
Qed.

(** The slot's first-call obligation, in the frame's form ([GI0 : forall mem, G_img segs G mem -> GI 0 [] mem],
    lib/AgreeTop.v, lib/ZComplete.v): when the slot's globals [G] hold the three heads, the image's bytes give
    the GI conjunct's first arm. *)
Lemma link_mf_gi0 : forall G, (forall a, mf_head_addr link_mf a -> in_globals G a) ->
  forall mem, G_img src0segs G mem -> mf_gi src0_msyms link_mf [] mem.
Proof.
  intros G HG mem Hi.
  assert (R : forall a, mf_head_addr link_mf a -> forall v, seg_rom src0segs (Z_to_bv 64 a) = v ->
    mbyte src0segs mem a = v) by (intros a Ha v <-; exact (Hi a (HG a Ha))).
  cbv [mf_head_addr mf_sink_addr mf_say_addr link_mf sk_ofl_head src0_sink_head src0_D_ofl_head] in R.
  left. split; [|reflexivity]. unfold mf_heads. change (ms_segs src0_msyms) with src0segs.
  cbv [mf_sink_addr mf_say_addr link_mf sk_ofl_head src0_sink_head src0_D_ofl_head].
  split; [|split]; intros k Hk;
    (do 8 (destruct k as [|k]; [apply R; [cbn; lia | vm_compute; reflexivity] |])); lia.
Qed.

Section t06.
Context {rc : YM05.RunCeil}.

(** A block for the FILE exists under link's own ceiling, whatever it is ([CEIL_MIN <= alloc_ceiling]). *)
Lemma link_mf_block_exists : exists f, 4096 <= f /\ f + MF_BLOCK <= alloc_ceiling /\ f mod 16 = 0 /\
  (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)).
Proof.
  pose proof alloc_ceiling_value as [[Hc _] _].
  exists 0x100000. split; [lia|]. split; [unfold MF_BLOCK; lia|]. split; [reflexivity|].
  intros i Hi Hin. apply link_in_img_range in Hin. unfold MF_BLOCK in Hi. lia.
Qed.

(** Every return after the first mark, for every block malloc may give fmemopen. *)
Lemma link_mf_returns : forall mem md f fl om wend wpos wbase pos len,
  4096 <= f -> f + MF_BLOCK <= alloc_ceiling -> f mod 16 = 0 ->
  (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)) ->
  fl = F_NORD \/ fl = F_NORD + F_ERR -> om = 0 \/ om = U32M1 ->
  (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
  (exists k, 0 <= k <= MF_BUFSIZ /\ wend = f + MF_BUF + MF_BUFSIZ /\ wpos = f + MF_BUF + k /\ wbase = f + MF_BUF) ->
  0 <= pos <= len -> len <= mf_size link_mf ->
  mf_gi src0_msyms link_mf [(f, MF_BLOCK)] (mf_state link_mf mem f fl om wend wpos wbase pos len) /\
  (closed_stdio_env src0_msyms mem -> Namei.fd_names_path (m_fds md) sink_path = false ->
   mf_sink src0_msyms link_mf (mf_state link_mf mem f fl om wend wpos wbase pos len) md).
Proof.
  intros mem md f fl om wend wpos wbase pos len Hf0 Hf1 Hf2 Hfi Hfl Hom Hw Hp Hl.
  pose proof alloc_ceiling_value as [[_ Hc] _].
  assert (HP : mf_place link_mf f) by (apply link_mf_place; [lia | lia | exact Hf2 | exact Hfi]).
  split.
  - apply (mf_state_gi (SH:=src0_sink_head) (SK:=src0_sink) src0_msyms link_mf);
      [exact HP | exact link_heads_ok | exact Hfl | exact Hom | exact Hw | exact Hp | exact Hl].
  - intros He Hn. apply (mf_state_sink (SH:=src0_sink_head) (SK:=src0_sink) src0_msyms link_mf);
      [exact HP | exact link_heads_ok | exact Hfl | exact Hom | exact Hw | exact Hp | exact Hl | exact He | exact Hn].
Qed.

(** The T0.6 lemma (see the head of this file for what each part says). *)
Theorem link_mf_t06 :
  code_list_ok src0tbl link_mf_code = true /\
  (forall mem,
     (forall a, mf_head_addr link_mf a \/ a = @sk_threaded src0_sink \/
        (@sk_ofl_lock src0_sink <= a < @sk_ofl_lock src0_sink + 4) ->
        mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
     mf_gi src0_msyms link_mf [] mem /\ closed_stdio_env src0_msyms mem) /\
  (forall G, (forall a, mf_head_addr link_mf a -> in_globals G a) ->
     forall mem, G_img src0segs G mem -> mf_gi src0_msyms link_mf [] mem) /\
  (forall mem md f fl om wend wpos wbase pos len,
     4096 <= f -> f + MF_BLOCK <= alloc_ceiling -> f mod 16 = 0 ->
     (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i)) ->
     fl = F_NORD \/ fl = F_NORD + F_ERR -> om = 0 \/ om = U32M1 ->
     (wend = 0 /\ wpos = 0 /\ wbase = 0) \/
     (exists k, 0 <= k <= MF_BUFSIZ /\ wend = f + MF_BUF + MF_BUFSIZ /\ wpos = f + MF_BUF + k /\ wbase = f + MF_BUF) ->
     0 <= pos <= len -> len <= mf_size link_mf ->
     mf_gi src0_msyms link_mf [(f, MF_BLOCK)] (mf_state link_mf mem f fl om wend wpos wbase pos len) /\
     (closed_stdio_env src0_msyms mem -> Namei.fd_names_path (m_fds md) sink_path = false ->
      mf_sink src0_msyms link_mf (mf_state link_mf mem f fl om wend wpos wbase pos len) md)) /\
  (exists f, 4096 <= f /\ f + MF_BLOCK <= alloc_ceiling /\ f mod 16 = 0 /\
     (forall i, 0 <= i < MF_BLOCK -> ~ in_img src0_msyms (f + i))) /\
  (forall mem f, memfile_at src0_msyms link_mf mem f ->
     val_mem src0segs mem (f + 140) 4 U32M1 /\ val_mem src0segs mem (f + 72) 8 (mf_write link_mf) /\
     val_mem src0segs mem (f + 8) 8 0 /\ val_mem src0segs mem (f + 16) 8 0 /\ val_mem src0segs mem (f + 112) 8 0) /\
  link_mwrite_closure = true /\
  code_list_ok src0tbl link_mwrite_stores = true /\
  stores_listed src0tbl (map fst link_mwrite_stores) 0x19544 69 = true.
Proof.
  split; [exact link_mf_code_ok|].
  split; [exact link_mf_start|].
  split; [exact link_mf_gi0|].
  split; [exact link_mf_returns|].
  split; [exact link_mf_block_exists|].
  split; [intros mem f H; exact (memfile_close_reads src0_msyms link_mf mem f H)|].
  split; [exact link_mwrite_closure_ok|].
  split; [exact link_mwrite_stores_ok | exact link_mwrite_has_only].
Qed.

End t06.
