(* Satisfiability witnesses of the function-specific Pre of the fifteen image-A helper contracts
   (lib/A/Prog/{check_refused,check_verdict,check_write,check_mark,text_buf,check_socket,index_of,check_bounds,
   check_read,check_requests,check_marks,model_read,model_write}_c.v here; talk_c.v and text_of_c.v in PART B at
   the end of this file, every name of which starts with hb_ / HB_), at registers and memories holding the values
   a real run of image A (fuzz_link.asan 059dae63e07c) holds at the call, as lib/A/Prog/form_witness.v does for
   fuzz_close and copy_attr. The journal part of each Pre (link_amem.v
   `apre`) needs AR of image A's start state (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f)). Each lemma
   holds for every segment list: the witness memory holds every byte its Pre reads, so no ROM byte is read.

   REGISTER-ONLY PRE (any memory):
   - check_refused_apre_sat: a0 = a1 = w64 1 (op_read, LLVMFuzzerTestOneInput 0x836ec: a refused read after an
     earlier exchange, g_nl.opened = 1 before and after).
   - check_verdict_apre_sat: a0 = a1 = w64 0 (op_decide: kind "" and alias "", V_MARK from both deciders).
   - check_write_apre_sat, check_mark_apre_sat (both `check_rc_apre`): a0 = a1 = w64 (-22) (op_write of a NULL name;
     op_refused); w64 (-22) <> w64 RC_FAILS.
   - text_buf_apre_sat: a0 = 16 (op_read 0x835f4, kc = 16). Its conjunct `text_buf_traces B CTX` is a HYPOTHESIS of
     the lemma: it is a fact of the start-up universe ACej.v and of B, which are not on this branch.

   RUN R (op_read). The first op of an input: op byte 0 (op_read), name byte 0 (name_of: g_names[0] = "nl0"),
   kc = ac = 16, then kernel(): flags 0, e and end_errno from byte 0 (nl_errno(0) = 105), one chunk made of one
   message of kind 1 (msg_build: nl_error(w, 0, -1), a 36-byte NLMSG_ERROR with code 0). model_read owes req_read 2
   (index_of "nl0" = 2) and talk answers 0 from chunk 0; reac_link_alias_read opens fd 7, sends the same 32 bytes,
   receives chunk 0, answers 0 and closes. The calls after it (fuzz_link.c:688-697) all see the same memory:
   check_socket 0x836b0, index_of 0x836d8 (the refusal test), check_bounds 0x836fc (kind), check_read,
   check_requests. The memory `HW_M` (the regions `rd_rgs hw_bs`):
   - g_nl at LA_G_NL (`hw_bs`, 271992 bytes): chunk[0] = the ACK (len 36, type 2, seq 1), chunk_len[0] = 36,
     n_chunks = next = 1, end_errno = 105, socket_errno = send_errno = 0, open = 0, opened = closed = 1, misuse = 0,
     sent[0] = req_read 2, sent_len[0] = 32, n_sent = 1, the table of interfaces() (fuzz_link.c:83-100):
     if_name[j] = &g_names[k], if_index[j] = k + 2 for the 60 k < 64 with k % 16 <> 15, then odd[1..4] with indices
     101..104, n_if = 64; every other byte 0;
   - g_names (512 bytes at LA_G_NAMES): slot k = "nl<k>", NUL-padded to 8 bytes;
   - .rodata [0x20fc0, 0x21080): the six strings of odd[] ("", "enp131s0.33", "eth0", "wlan0", "veth-box", "gone0"),
     each in a 32-byte slot. odd[1..4] = 0x20fe0, 0x21000, 0x21020, 0x21040: the data words at LA_ODD + 8 .. + 32 of
     .data.rel.ro in the unstripped twin (sha256 66cd0f159895...), read with pyelftools 0.33 (2026-10-30);
   - kind at HW_KB = 0x602000000010 and alias at HW_AB = 0x602000000040: two malloc(17) blocks (48-byte chunks with a
     16-byte header), each [0; 0x5a x 16] (text_buf's memset, then reac_link_alias_read's NUL at [0]);
   - wk at HW_WK and wa at HW_WA: offsets 736 and 816 of LLVMFuzzerTestOneInput's 896-byte class-4 side frame at
     HW_F4 = 0x7f0000002000 (frame_alloc_4 after +0x6c `addi a0, zero, 0x380`; the frame description string at
     .rodata 0x1672f reads "... 736 40 8 wk.i:684 816 40 8 wa.i:684"), 40 zero bytes each;
   - the model block at HW_MB = 0x602000001000 (calloc(1, 8856), `rd_md`): socket_errno = send_errno = 0, next = 1,
     req[0] = req_read 2, req_len[0] = 32, n_req = 1, no mark;
   - the shadow bytes the Pre's read, with the values of the run: g_nl's 33999 granules 0 and its first redzone byte
     f9; g_names' 64 granules 0; the 24 shadow bytes of the six strings, from their asan_globals descriptors (sizes
     1, 12, 5, 6, 9, 6 in 32-byte slots): 01 f9 f9 f9 | 00 04 f9 f9 | 05 f9 f9 f9 | 06 f9 f9 f9 | 00 01 f9 f9 |
     06 f9 f9 f9; the two heap chunks: fa fa 00 00 01 fa fa fa 00 00 01 fa fa fa fa fa (header, the 17 bytes, tail;
     fa marks heap bytes unusable); the side frame's granules 84..111: f2 x 8 | 00 x 5 (wk) | f2 x 5 | 00 x 5 (wa) |
     f3 x 5; the model block's 1107 granules 0 and the 5 bytes fa after them.
   Lemmas at R (sp = HW_SP = 0x7fffffffee60, LLVMFuzzerTestOneInput's realigned sp from the entry sp SP0 =
   0x7ffffffff000, as talk_c.v and model_read_c.v state it; all of R's calls are made at this sp):
   - check_socket_apre_sat: at HW_M.
   - index_of_apre_sat: a0 = LA_G_NAMES ("nl0"); the 64 entries of aiftab_at by a decidable check (`ent_chk`,
     `ift_chk`) and one soundness lemma (`hw_entry`).
   - check_bounds_apre_sat: a0 = HW_KB, a1 = 16 (bs = [0; 0x5a x 15], guard 0x5a).
   - check_read_apre_sat: a0 = a1 = w64 0, a2 = HW_KB, a3 = HW_WK, a4 = HW_AB, a5 = HW_WA (four empty strings).
   - check_requests_apre_sat: a0 = HW_MB.
   The fields of g_nl come from ONE vm_compute over the list (`hw_check_ok`); every other proof is over an abstract
   list with the fields as hypotheses (form_witness.v's warning).
   STRCMP TAILS (lib/A/Rt/RtString.v `atail_vis`, astrcmp_arg's last conjunct): every string a strcmp reads has the
   bytes after its NUL to the end of the NUL's granule in the witness memory: g_names' slots (NUL-padded to 8),
   odd's and texts' 32-byte .rodata slots, the heap blocks' 17 bytes ("" at [0]), wk and wa (40 bytes). `tail_chk`
   checks them inside `sarg_chk`.

   RUN M (op_mark). op_mark of "nl0" as the first op, kernel() with two ACK chunks: model_mark reads (ACK: kind and
   alias "", V_MARK), writes "reac-pw:served" (ACK) and remembers "nl0"; mark_quietly does the same. At the
   check_marks call, `MK_M` holds the marks block at HW_MKB = 0x602000004000 (calloc(1, 516): n = 1, name[0] = "nl0"),
   the model block at HW_MB (next = 2, req[0] = req_read 2, req[1] = req_write 2 "reac-pw:served", req_len = 32, 52,
   n_req = 2, mark[0] = "nl0", n_mark = 1), their shadow (marks: 64 granules 0, then 04, then fa x 7; model as in R),
   and the marks chunk's tail [HW_MKB + 516, HW_MKB + 520): 4 bytes 0 (calloc rounds the chunk to the granule).
   - check_marks_apre_sat: a0 = HW_MKB, a1 = HW_MB, sp = HW_SP.

   RUN R0 (run R at model_read, LLVMFuzzerTestOneInput 0x8368c, before the library call). kernel() has queued the
   ACK chunk and model_begin has run; no socket was opened yet. The memory `PR_M` (the regions `pr_rgs pr_bs`):
   - g_nl (`pr_bs`): chunk[0] = the ACK, chunk_len[0] = 36, n_chunks = 1, next = 0, end_errno = 105,
     socket_errno = send_errno = 0, open = opened = closed = misuse = 0, sent and sent_len all 0, n_sent = 0, the
     interfaces() table and n_if = 64 as in R;
   - the model block at HW_MB after model_begin: all 8856 bytes 0 (next = 0, n_req = 0, no mark);
   - wk, wa: their 40 zero bytes (checked_memset at LLVMFuzzerTestOneInput +0xe58, +0xe80) and the frame shadow of R;
   - g_names, odd's strings, g_nl's and the model block's shadow as in R.
   - model_read_apre_sat: a0 = HW_MB, a1 = LA_G_NAMES ("nl0"), a2 = HW_WK, a3 = 16, a4 = HW_WA, a5 = 16, sp = HW_SP;
     the hypothesis HERR (ERRNO below).
   RUN W (op_write as the first op, LLVMFuzzerTestOneInput 0x83858, model_write before the library call): op byte
   1, name byte 0 ("nl0"), text byte 1 (texts[1] = "reac-pw:served", A_SERVED = 0x21100, the data word at
   LA_TEXTS + 8 of .data.rel.ro in the unstripped twin, read with pyelftools 0.33), then kernel() as in R. The
   memory `PW_M` (`pw_rgs pr_bs`): g_nl and the model block as in R0; .rodata [0x21100, 0x21140): "reac-pw:served"
   and "reac-pw:minted", each NUL-padded in a 32-byte slot; their shadow 00 07 f9 f9 | 00 07 f9 f9 (asan_globals:
   sizes 15 and 15, 32-byte slots); g_names, odd's strings and the other shadow as in R. strlen's slack is the one
   byte 0 at 0x2110f.
   - model_write_apre_sat: a0 = HW_MB, a1 = LA_G_NAMES ("nl0"), a2 = A_SERVED, sp = HW_SP; the hypothesis HERR
     (ERRNO below).

   ERRNO (model_read_apre_sat, model_write_apre_sat, and hb_text_of_apre_sat in PART B). These three Pres say that
   the bytes their Post gives back across a callee are not errno bytes, `apart (as_errno B) 4 obj n`, because the
   callee keeps only bytes outside [as_errno B, as_errno B + 4): the image clause of `akept` (index_of's `apost`)
   excepts them, and so does the malloc rule's kept clause (`ascratch`, Reusable/YG0d.v:216-217). The objects:
   model_read's model block and two buffers, model_write's model block, text_of's cursor. No memory
   places the abstract `as_errno B`, so each of the three lemmas takes ONE hypothesis of the instance,
     HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd,
   the first conjunct of `api_env` (Reusable/YCbq.v:807). Every such object of these witnesses is above
   kLowMemEnd = 0x7fff8000 (HW_MB, HW_WK, HW_WA; HB_TX_P, HB_TX_O), so each `apart` holds by its left disjunct. The
   instance discharges HERR by `tl_errno` of `TfibLib` (A/ACeg.v:49, A/ACeh.v:49; `proj1 (tl_env B TL)`): errno is
   the image word as_errno B = TFIB_ERRNO = 0x631b6c = TFIB_TP - 164 (A/AF0m.v:16, 21, `ts_errno`), in low memory.

   The heap and side-frame addresses are one choice the allocator can make (16-aligned, high memory, below
   alloc_ceiling); the run fixes the contents and the shadow layout, not these addresses.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem form_witness
  index_of_c check_socket_c check_refused_c check_bounds_c check_read_c check_requests_c check_write_c
  check_mark_c check_marks_c check_verdict_c text_buf_c model_read_c model_write_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Lists and little-endian bytes
   ========================================================================== *)

Lemma nth_error_firstn' : forall (A : Type) n (l : list A) k,
  (k < n)%nat -> nth_error (firstn n l) k = nth_error l k.
Proof.
  intros A n. induction n as [|n IH]; intros l k Hk; [lia|].
  destruct l as [|a l]; [reflexivity|].
  destruct k as [|k]; [reflexivity|]. cbn [firstn nth_error]. apply IH. lia.
Qed.

Lemma nth_error_skipn' : forall (A : Type) n (l : list A) k,
  nth_error (skipn n l) k = nth_error l (n + k).
Proof.
  intros A n. induction n as [|n IH]; intros l k; [reflexivity|].
  destruct l as [|a l]; [destruct k; reflexivity|]. cbn [skipn nth_error Nat.add]. apply IH.
Qed.

Lemma nth_error_seq' : forall len s k, (k < len)%nat -> nth_error (seq s len) k = Some (s + k)%nat.
Proof.
  induction len as [|len IH]; intros s k Hk; [lia|].
  destruct k as [|k]; cbn [seq nth_error].
  - f_equal. lia.
  - rewrite IH by lia. f_equal. lia.
Qed.

Lemma slice_nth : forall (l : list byte) off n k, (k < Z.to_nat n)%nat ->
  nth_error (slice l off n) k = nth_error l (Z.to_nat off + k).
Proof. intros l off n k Hk. unfold slice. rewrite nth_error_firstn' by exact Hk. apply nth_error_skipn'. Qed.

(* the n little-endian bytes of v, as val_mem states them (Reusable/YI04.v:141-142) *)
Definition lbytes (n : nat) (v : Z) : list byte := map (fun k => Z_to_bv 8 (YO0f.le_byte v n k)) (seq 0 n).

Lemma lbytes_nth : forall n v k, (k < n)%nat -> nth_error (lbytes n v) k = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Proof. intros n v k Hk. unfold lbytes. rewrite nth_error_map, nth_error_seq' by exact Hk. reflexivity. Qed.

Lemma le_byte_bit : forall v k j, 0 <= j < 8 ->
  Z.testbit (YO0f.le_byte v 8 k) j = Z.testbit (v mod 2 ^ 64) (8 * Z.of_nat k + j).
Proof.
  intros v k j Hj. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. change 256 with (2 ^ 8).
  rewrite (Z.mod_pow2_bits_low (Z.shiftr (v mod 2 ^ 64) (8 * Z.of_nat k)) 8 j) by lia.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

(* eight bytes fix a value in [0, 2^64) *)
Lemma le_byte8_inj : forall p q, (forall k, (k < 8)%nat -> YO0f.le_byte p 8 k = YO0f.le_byte q 8 k) ->
  0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros p q H Hp Hq.
  rewrite <- (Z.mod_small p (2 ^ 64)) by exact Hp. rewrite <- (Z.mod_small q (2 ^ 64)) by exact Hq.
  apply Z.bits_inj'. intros n Hn. destruct (Z.lt_ge_cases n 64) as [Hl|Hg].
  - assert (E : n = 8 * Z.of_nat (Z.to_nat (n / 8)) + n mod 8).
    { rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_mod. lia. }
    rewrite E.
    rewrite <- (le_byte_bit p (Z.to_nat (n / 8)) (n mod 8)) by (apply Z.mod_pos_bound; lia).
    rewrite <- (le_byte_bit q (Z.to_nat (n / 8)) (n mod 8)) by (apply Z.mod_pos_bound; lia).
    rewrite H; [reflexivity|]. lia.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma val_mem8_inj : forall segs m a p q, val_mem segs m a 8 p -> val_mem segs m a 8 q ->
  0 <= p < 2 ^ 64 -> 0 <= q < 2 ^ 64 -> p = q.
Proof.
  intros segs m a p q Hp Hq Hpr Hqr. apply le_byte8_inj; [|exact Hpr|exact Hqr].
  intros k Hk. specialize (Hp k Hk). specialize (Hq k Hk). rewrite Hp in Hq.
  assert (E : bv_unsigned (Z_to_bv 8 (YO0f.le_byte p 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte q 8 k)))
    by congruence.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite !Z.mod_small in E by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia). exact E.
Qed.

Fixpoint bll_eqb (a b : list (list byte)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => bl_eqb x y && bll_eqb a' b'
  | _, _ => false
  end.

Lemma bll_eqb_eq : forall a b, bll_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [bll_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hx Ha]. rewrite (bl_eqb_eq x y Hx), (IH b Ha). reflexivity.
Qed.

(* s, NUL-padded to n bytes *)
Definition pad (n : nat) (s : list byte) : list byte := s ++ repeat (zb 0) (n - length s).

(* ==========================================================================
   2. Memories as lists of disjoint regions: n bytes of v (RF), or n bytes of a list (RL)
   ========================================================================== *)

Inductive rg : Type := RF (lo n v : Z) | RL (lo n : Z) (l : list byte).
Definition rg_lo (r : rg) : Z := match r with RF lo _ _ => lo | RL lo _ _ => lo end.
Definition rg_n (r : rg) : Z := match r with RF _ n _ => n | RL _ n _ => n end.
Definition rg_val (r : rg) (a : Z) : option byte :=
  match r with RF _ _ v => Some (zb v) | RL lo _ l => nth_error l (Z.to_nat (a - lo)) end.
Fixpoint rlook (rs : list rg) (a : Z) : option byte :=
  match rs with
  | [] => None
  | r :: t => if inrz a (rg_lo r) (rg_n r) then rg_val r a else rlook t a
  end.
Definition rmem (rs : list rg) : word -> option byte := fun w => rlook rs (bv_unsigned w).
Definition rg_apart (r r' : rg) : bool :=
  (rg_lo r + rg_n r <=? rg_lo r') || (rg_lo r' + rg_n r' <=? rg_lo r).
Fixpoint rgs_disj (rs : list rg) : bool :=
  match rs with [] => true | r :: t => forallb (rg_apart r) t && rgs_disj t end.

Lemma rlook_in : forall rs r a, rgs_disj rs = true -> In r rs ->
  rg_lo r <= a < rg_lo r + rg_n r -> rlook rs a = rg_val r a.
Proof.
  induction rs as [|h t IH]; intros r a Hd Hin Ha; [destruct Hin|].
  cbn [rgs_disj] in Hd. apply andb_prop in Hd as [Hh Ht]. cbn [rlook]. cbn [In] in Hin.
  destruct Hin as [<-|Hin].
  - rewrite inrz_true by lia. reflexivity.
  - rewrite forallb_forall in Hh. specialize (Hh r Hin). unfold rg_apart in Hh.
    rewrite inrz_false by (apply orb_prop in Hh as [Hh|Hh]; apply Z.leb_le in Hh; lia).
    exact (IH r a Ht Hin Ha).
Qed.

Lemma rmem_at : forall rs r a, rgs_disj rs = true -> In r rs ->
  rg_lo r <= a < rg_lo r + rg_n r -> 0 <= a < 2 ^ 64 -> rmem rs (Z_to_bv 64 a) = rg_val r a.
Proof.
  intros rs r a Hd Hin Ha Hw. unfold rmem. rewrite unsigned_lit_small by exact Hw.
  exact (rlook_in rs r a Hd Hin Ha).
Qed.

(* m holds every byte m0 holds *)
Definition mext (m0 m : word -> option byte) : Prop := forall w b, m0 w = Some b -> m w = Some b.
Lemma mext_refl : forall m, mext m m.
Proof. intros m w b H. exact H. Qed.

Lemma rl_au8arr : forall segs rs m lo n l, mext (rmem rs) m -> rgs_disj rs = true -> In (RL lo n l) rs ->
  Z.of_nat (length l) = n -> 0 <= lo -> lo + n <= 2 ^ 64 -> au8arr segs m lo l.
Proof.
  intros segs rs m lo n l Hx Hd Hin Hl H0 H1.
  assert (Hat : forall i, (i < length l)%nat -> m (Z_to_bv 64 (lo + Z.of_nat i)) = nth_error l i).
  { intros i Hi. destruct (nth_error l i) as [b|] eqn:E; [|apply nth_error_None in E; lia].
    apply Hx. rewrite (rmem_at rs (RL lo n l) (lo + Z.of_nat i) Hd Hin) by (cbn [rg_lo rg_n]; lia).
    cbn [rg_val]. replace (lo + Z.of_nat i - lo) with (Z.of_nat i) by lia. rewrite Nat2Z.id. exact E. }
  split.
  - split; [exact H0|]. split; [lia|]. intros i Hi. unfold mbyte. rewrite (Hat i Hi).
    destruct (nth_error l i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  - intros i Hi. unfold writable_at, wview. replace (lo + i) with (lo + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (Hat (Z.to_nat i) ltac:(lia)).
    destruct (nth_error l (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|].
    apply nth_error_None in E. lia.
Qed.

(* a range whose shadow bytes lie in a region of zeros *)
Lemma ra_fill : forall segs rs m lo n a len, mext (rmem rs) m -> rgs_disj rs = true -> In (RF lo n 0) rs ->
  0 <= lo -> lo + n <= 2 ^ 64 ->
  (forall x, a <= x < a + len -> lo <= shadow_addr x < lo + n) ->
  range_addressable (ard segs m) SHADOW_OFF a len.
Proof.
  intros segs rs m lo n a len Hx Hd Hin H0 H1 Hs x Hr. exists 0. split; [|left; reflexivity].
  specialize (Hs x Hr). unfold ard, mbyte, shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
  rewrite (Hx _ (zb 0)); [reflexivity|].
  rewrite (rmem_at rs (RF lo n 0) (shadow_addr x) Hd Hin) by (cbn [rg_lo rg_n]; lia). reflexivity.
Qed.

(* the shadow bytes of [a, a + len), a 8-aligned, lie in [lo, lo + n). Stated over abstract numbers: lia with the
   division by 8 and the image's 2^43-sized constants ran for over a minute per call. *)
Lemma shadow_in : forall a len x, a mod 8 = 0 -> a <= x < a + len ->
  shadow_addr a <= shadow_addr x < shadow_addr a + (len + 7) / 8.
Proof. intros a len x Ha Hx. unfold shadow_addr. lia. Qed.

Lemma shadow_win : forall a len lo n x, a mod 8 = 0 -> lo <= shadow_addr a ->
  shadow_addr a + (len + 7) / 8 <= lo + n -> a <= x < a + len -> lo <= shadow_addr x < lo + n.
Proof. intros a len lo n x Ha H1 H2 Hx. pose proof (shadow_in a len x Ha Hx). lia. Qed.

(* a closed comparison, by computation. (lia in a context that holds a closed term over a long list, e.g.
   `Z.of_nat (length rd_md) = MD_SIZE`, ran for tens of seconds per call, so closed goals never go to lia.) *)
Ltac zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac zlt := apply Z.ltb_lt; vm_compute; reflexivity.

(* ==========================================================================
   3. Decidable checks over a memory function, and their soundness
   ========================================================================== *)

Definition rdz (m : word -> option byte) (a : Z) : option byte := m (Z_to_bv 64 a).
Definition ob_is (o : option byte) (b : byte) : bool := match o with Some c => bz c =? bz b | None => false end.
Fixpoint bytes_chk (m : word -> option byte) (a : Z) (l : list byte) : bool :=
  match l with [] => true | b :: t => ob_is (rdz m a) b && bytes_chk m (a + 1) t end.

Lemma ob_is_ok : forall o b, ob_is o b = true -> o = Some b.
Proof.
  intros [c|] b H; unfold ob_is in H; [|discriminate].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H.
Qed.

Lemma bytes_chk_ok : forall m0 m l a, mext m0 m -> bytes_chk m0 a l = true ->
  forall i, (i < length l)%nat -> m (Z_to_bv 64 (a + Z.of_nat i)) = nth_error l i.
Proof.
  intros m0 m l. induction l as [|b t IH]; intros a Hx Hc i Hi; [cbn [length] in Hi; lia|].
  cbn [bytes_chk] in Hc. apply andb_prop in Hc as [Hb Ht].
  destruct i as [|i]; cbn [nth_error].
  - apply Hx. replace (a + Z.of_nat 0) with a by lia. exact (ob_is_ok _ _ Hb).
  - replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    apply (IH (a + 1) Hx Ht). cbn [length] in Hi. lia.
Qed.

Lemma abytes_chk : forall segs m0 m a l, mext m0 m -> bytes_chk m0 a l = true ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> abytes segs m a l.
Proof.
  intros segs m0 m a l Hx Hc H0 H1. split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mbyte. rewrite (bytes_chk_ok m0 m l a Hx Hc i Hi).
  destruct (nth_error l i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma awrange_chk : forall segs m0 m a l, mext m0 m -> bytes_chk m0 a l = true ->
  awrange segs m a (Z.of_nat (length l)).
Proof.
  intros segs m0 m a l Hx Hc i Hi. unfold writable_at, wview.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (bytes_chk_ok m0 m l a Hx Hc (Z.to_nat i) ltac:(lia)).
  destruct (nth_error l (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|]. apply nth_error_None in E. lia.
Qed.

Lemma au8arr_chk : forall segs m0 m a l, mext m0 m -> bytes_chk m0 a l = true ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> au8arr segs m a l.
Proof.
  intros segs m0 m a l Hx Hc H0 H1.
  split; [exact (abytes_chk segs m0 m a l Hx Hc H0 H1) | exact (awrange_chk segs m0 m a l Hx Hc)].
Qed.

Definition nonul (s : list byte) : bool := forallb (fun b => negb (bz b =? 0)) s.
Definition cstr_chk (m : word -> option byte) (a : Z) (s : list byte) : bool :=
  (0 <=? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 64) && bytes_chk m a (s ++ [zb 0]) && nonul s.

Lemma acstr_chk : forall segs m0 m a s, mext m0 m -> cstr_chk m0 a s = true -> acstr_at segs m a s.
Proof.
  intros segs m0 m a s Hx Hc. unfold cstr_chk in Hc. repeat rewrite andb_true_iff in Hc.
  destruct Hc as [[[H0 H1] H2] H3]. apply Z.leb_le in H0, H1.
  split.
  - apply (abytes_chk segs m0 m a (s ++ [zb 0]) Hx H2 H0). rewrite length_app. cbn [length]. lia.
  - intros Hin. unfold nonul in H3. rewrite forallb_forall in H3. specialize (H3 _ Hin).
    cbv in H3. discriminate.
Qed.

Definition saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Fixpoint zall (f : Z -> bool) (fuel : nat) (x : Z) : bool :=
  match fuel with O => true | S k => f x && zall f k (x + 1) end.

Lemma zall_ok : forall f fuel x y, zall f fuel x = true -> x <= y < x + Z.of_nat fuel -> f y = true.
Proof.
  intros f fuel. induction fuel as [|k IH]; intros x y H Hy; [lia|].
  cbn [zall] in H. apply andb_prop in H as [Hx Hk].
  destruct (Z.eq_dec y x) as [->|Ne]; [exact Hx|]. apply (IH (x + 1) y Hk). lia.
Qed.

Definition sa_ok (m : word -> option byte) (x : Z) : bool :=
  match rdz m (shadow_addr x) with Some s => saddr_okb x (bz s) | None => false end.
Definition ra_chk (m : word -> option byte) (a n : Z) : bool := zall (sa_ok m) (Z.to_nat n) a.

Lemma ra_chk_ok : forall segs m0 m a n, mext m0 m -> ra_chk m0 a n = true ->
  range_addressable (ard segs m) SHADOW_OFF a n.
Proof.
  intros segs m0 m a n Hx Hc x Hr. unfold ra_chk in Hc.
  pose proof (zall_ok _ _ _ x Hc ltac:(lia)) as H. unfold sa_ok, rdz in H.
  destruct (m0 (Z_to_bv 64 (shadow_addr x))) as [s|] eqn:E; [|discriminate].
  exists (bz s). split.
  - unfold ard, mbyte, shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
    rewrite (Hx _ _ E). reflexivity.
  - unfold saddr_okb in H. unfold saddr_ok. apply orb_prop in H as [H|H]; [left; apply Z.eqb_eq; exact H|].
    right. apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1, H2. lia.
Qed.

Definition isSomeb (o : option byte) : bool := match o with Some _ => true | None => false end.
Definition hull_lo (x : Z) : Z := shadow_addr x / 8 * 8.
Definition hull_hi (x n : Z) : Z := shadow_addr (x + n - 1) / 8 * 8 + 8.
Definition hull_chk (m : word -> option byte) (x n : Z) : bool :=
  zall (fun s => isSomeb (rdz m s)) (Z.to_nat (hull_hi x n - hull_lo x)) (hull_lo x).

Lemma hull_chk_ok : forall segs m0 m x n, mext m0 m -> hull_chk m0 x n = true ->
  shadow_hull_vis (ard segs m) x n.
Proof.
  intros segs m0 m x n Hx Hc s Hs. unfold hull_chk in Hc.
  pose proof (zall_ok _ _ _ s Hc) as H. unfold hull_lo, hull_hi in H. specialize (H ltac:(lia)).
  cbv beta in H. unfold rdz, isSomeb in H. destruct (m0 (Z_to_bv 64 s)) as [b|] eqn:E; [|discriminate].
  unfold ard, mbyte. rewrite (Hx _ _ E). cbn [option_map]. discriminate.
Qed.

Definition amem_rangeb (p n : Z) : bool :=
  (p + n <=? kLowMemEnd - 1) || ((kHighMemBeg <=? p) && (p + n <=? kHighMemEnd - 1)).

Lemma amem_rangeb_ok : forall p n, amem_rangeb p n = true -> amem_range p n.
Proof.
  intros p n H. unfold amem_rangeb in H. unfold amem_range.
  apply orb_prop in H as [H|H]; [left; apply Z.leb_le; exact H|].
  right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

(* bytes [lo, hi) all present *)
Definition pres_chk (m : word -> option byte) (lo hi : Z) : bool :=
  zall (fun a => isSomeb (rdz m a)) (Z.to_nat (hi - lo)) lo.

Lemma pres_chk_ok : forall segs m0 m lo hi, mext m0 m -> pres_chk m0 lo hi = true ->
  forall b, lo <= b < hi -> ard segs m b <> None.
Proof.
  intros segs m0 m lo hi Hx Hc b Hb. unfold pres_chk in Hc.
  pose proof (zall_ok _ _ _ b Hc ltac:(lia)) as H. cbv beta in H.
  unfold rdz, isSomeb in H. destruct (m0 (Z_to_bv 64 b)) as [c|] eqn:E; [|discriminate].
  unfold ard, mbyte. rewrite (Hx _ _ E). cbn [option_map]. discriminate.
Qed.

(* the strcmp wrapper's `atail_vis` of a string s at p (lib/A/Rt/RtString.v): the bytes after its NUL to the end of
   the NUL's 8-byte granule present *)
Definition tail_chk (m : word -> option byte) (p : Z) (s : list byte) : bool :=
  pres_chk m (p + Z.of_nat (length s) + 1) (p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8).

Lemma tail_chk_ok : forall segs m0 m p s, mext m0 m -> tail_chk m0 p s = true ->
  forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
    ard segs m a <> None.
Proof. intros segs m0 m p s Hx Hc a Ha. apply (pres_chk_ok segs m0 m _ _ Hx Hc). lia. Qed.

(* the facts astrcmp_arg (index_of_c.v) asks of a string s at p, at stack pointer sp and bound K *)
Definition sarg_chk (m : word -> option byte) (sp K p : Z) (s : list byte) : bool :=
  (0 <? p) && (Z.of_nat (length s) + 1 <? 2 ^ 32) && amem_rangeb p (Z.of_nat (length s) + 1) &&
  ra_chk m p (Z.of_nat (length s) + 1) && hull_chk m p (Z.of_nat (length s) + 1) &&
  ((p + (Z.of_nat (length s) + 1) <=? sp - K) || (sp <=? p)) && tail_chk m p s.

Lemma sarg_chk_ok : forall segs regs m0 m sp K p s, mext m0 m -> spZ regs = sp ->
  sarg_chk m0 sp K p s = true -> astrcmp_arg segs regs K m p s.
Proof.
  intros segs regs m0 m sp K p s Hx Hsp Hc. unfold sarg_chk in Hc.
  repeat rewrite andb_true_iff in Hc. destruct Hc as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Z.ltb_lt in H1, H2. unfold astrcmp_arg.
  split; [exact H1|]. split; [exact H2|]. split; [exact (amem_rangeb_ok _ _ H3)|].
  split; [exact (ra_chk_ok segs m0 m _ _ Hx H4)|]. split; [exact (hull_chk_ok segs m0 m _ _ Hx H5)|].
  split; [unfold apart_frame; rewrite Hsp; apply orb_prop in H6 as [H6|H6]; apply Z.leb_le in H6; lia|].
  exact (tail_chk_ok segs m0 m p s Hx H7).
Qed.

(* ==========================================================================
   4. The Pre's that read only registers
   ========================================================================== *)

Lemma w64_0_ne : w64 0 <> w64 RC_FAILS.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.
Lemma w64_m22_ne : w64 (-22) <> w64 RC_FAILS.
Proof. intros H. apply (f_equal bv_unsigned) in H. vm_compute in H. discriminate. Qed.

(* check_refused at op_read 0x836ec: opened before = opened after = 1 *)
Lemma check_refused_apre_sat : forall (regs : bvmap 5 word) (m : word -> option byte),
  getr regs 10 = w64 1 -> getr regs 11 = w64 1 -> check_refused_apre regs m.
Proof. intros regs m H10 H11. unfold check_refused_apre. rewrite H10, H11. reflexivity. Qed.

(* check_verdict at op_decide: V_MARK from both deciders *)
Lemma check_verdict_apre_sat : forall (regs : bvmap 5 word) (m : word -> option byte),
  getr regs 10 = w64 0 -> getr regs 11 = w64 0 -> check_verdict_apre regs m.
Proof. intros regs m H10 H11. unfold check_verdict_apre. rewrite H10, H11. reflexivity. Qed.

(* check_write at op_write of a NULL name: both sides answer -EINVAL *)
Lemma check_write_apre_sat : forall (regs : bvmap 5 word) (m : word -> option byte),
  getr regs 10 = w64 (-22) -> getr regs 11 = w64 (-22) -> check_rc_apre regs m.
Proof.
  intros regs m H10 H11. unfold check_rc_apre, same_rc_aregs. split.
  - intros E. rewrite H11 in E. exfalso. exact (w64_m22_ne E).
  - intros _. rewrite H10, H11. reflexivity.
Qed.

(* check_mark at op_refused: mark_quietly answers -EINVAL, the call passes -EINVAL *)
Lemma check_mark_apre_sat : forall (regs : bvmap 5 word) (m : word -> option byte),
  getr regs 10 = w64 (-22) -> getr regs 11 = w64 (-22) -> check_rc_apre regs m.
Proof. exact check_write_apre_sat. Qed.

Section tb.
Variable B : asyms.
Variable CTX : list (list Z).
(* text_buf at op_read 0x835f4: cap = kc = 16; the trace conjunct waits for ACej.v and B *)
Lemma text_buf_apre_sat : forall (regs : bvmap 5 word) (m : word -> option byte),
  aarg regs 0 = 16 -> text_buf_traces B CTX -> text_buf_apre B CTX regs m.
Proof. intros regs m H0 Ht. unfold text_buf_apre. split; [rewrite H0; lia | exact Ht]. Qed.
End tb.

(* ==========================================================================
   5. Run R (op_read after reac_link_alias_read): the values
   ========================================================================== *)

Definition HW_SP : Z := 0x7fffffffee60.
Definition HW_KB : Z := 0x602000000010.
Definition HW_AB : Z := 0x602000000040.
Definition HW_F4 : Z := 0x7f0000002000.
Definition HW_WK : Z := 0x7f00000022e0.
Definition HW_WA : Z := 0x7f0000002330.
Definition HW_MB : Z := 0x602000001000.
Definition HW_MKB : Z := 0x602000004000.
Definition LA_ODD_STR : Z := 0x20fc0.
(* the shadow byte addresses of the objects *)
Definition S_NL : Z := 0x800b3958.
Definition S_GN : Z := 0x800bdf58.
Definition S_ODD : Z := 0x7fffc1f8.
Definition S_HEAP : Z := 0xc047fff8000.
Definition S_MB : Z := 0xc047fff8200.
Definition S_MKB : Z := 0xc047fff8800.
Definition S_F4 : Z := 0xfe07fff8400.

Lemma hw_consts : S_NL = shadow_addr LA_G_NL /\ S_GN = shadow_addr LA_G_NAMES /\
  S_ODD = shadow_addr LA_ODD_STR /\ S_HEAP = shadow_addr (HW_KB - 16) /\ S_MB = shadow_addr HW_MB /\
  S_MKB = shadow_addr HW_MKB /\ S_F4 = shadow_addr HW_F4 /\ HW_WK = HW_F4 + 736 /\ HW_WA = HW_F4 + 816 /\
  HW_AB = HW_KB + 48 /\ LA_ODD = 0xa1760.
Proof. vm_compute. repeat (match goal with |- _ /\ _ => split end); reflexivity. Qed.

(* "nl<k>" *)
Definition nl_name (k : nat) : list byte :=
  map zb ([110; 108] ++ (if Nat.ltb k 10 then [48 + Z.of_nat k]
                          else [48 + Z.of_nat (Nat.div k 10); 48 + Z.of_nat (Nat.modulo k 10)])).
Definition gn_bytes : list byte := List.flat_map (fun k => pad 8 (nl_name k)) (seq 0 64).

Definition s_enp : list byte := map zb [101; 110; 112; 49; 51; 49; 115; 48; 46; 51; 51].
Definition s_eth0 : list byte := map zb [101; 116; 104; 48].
Definition s_wlan0 : list byte := map zb [119; 108; 97; 110; 48].
Definition s_veth : list byte := map zb [118; 101; 116; 104; 45; 98; 111; 120].
Definition s_gone0 : list byte := map zb [103; 111; 110; 101; 48].
Definition odd_bytes : list byte := List.flat_map (pad 32) [[]; s_enp; s_eth0; s_wlan0; s_veth; s_gone0].
Definition odd_sh : list byte :=
  map zb [1; 0xf9; 0xf9; 0xf9; 0; 4; 0xf9; 0xf9; 5; 0xf9; 0xf9; 0xf9;
          6; 0xf9; 0xf9; 0xf9; 0; 1; 0xf9; 0xf9; 6; 0xf9; 0xf9; 0xf9].

(* the interface table interfaces() builds: (if_name[j], the string, if_index[j]) *)
Definition hw_ift : list (Z * list byte * Z) :=
  map (fun k => (LA_G_NAMES + 8 * Z.of_nat k, nl_name k, Z.of_nat k + 2))
      (List.filter (fun k => negb (Nat.eqb (Nat.modulo k 16) 15)) (seq 0 64))
  ++ [(0x20fe0, s_enp, 101); (0x21000, s_eth0, 102); (0x21020, s_wlan0, 103); (0x21040, s_veth, 104)].
(* (name, index) of each entry: an abbreviation, not a constant, so that no conversion has to unfold a constant
   against its body (the kernel then evaluated `map` over the table: hw_tab_ift's Qed ran past a minute) *)
Abbreviation hw_tab := (map (fun e : Z * list byte * Z => (snd (fst e), snd e)) hw_ift).
(* if_name[80] then if_index[80], 960 bytes *)
Definition hw_ift_bytes : list byte :=
  List.flat_map (fun e => lbytes 8 (fst (fst e))) hw_ift ++ zeros 128 ++
  List.flat_map (fun e => lbytes 4 (snd e)) hw_ift ++ zeros 64.
(* nl_error(w, 0, -1): len 36, type NLMSG_ERROR, flags 0, seq 1, pid 0, code 0, 16 zero bytes *)
Definition ack36 : list byte :=
  lbytes 4 36 ++ lbytes 2 NL_ERROR ++ lbytes 2 0 ++ lbytes 4 1 ++ lbytes 4 0 ++ zeros 20.

(* g_nl (netlink.h:48-68) after reac_link_alias_read *)
Definition hw_bs : list byte :=
  ack36 ++ zeros (NL_CHUNKS * NL_CHUNK_MAX - 36) ++         (* chunk *)
  lbytes 8 36 ++ zeros (8 * 63) ++                          (* chunk_len *)
  lbytes 4 1 ++ lbytes 4 1 ++ lbytes 4 105 ++ lbytes 4 0 ++ lbytes 4 0 ++   (* n_chunks next end socket send *)
  lbytes 4 0 ++ lbytes 4 1 ++ lbytes 4 1 ++ lbytes 4 0 ++   (* open opened closed misuse *)
  req_read 2 ++ zeros (NL_SENT_MAX * NL_SENT_LEN - 32) ++ zeros 4 ++   (* sent, padding *)
  lbytes 8 32 ++ zeros (8 * 15) ++                          (* sent_len *)
  lbytes 4 1 ++ zeros 4 ++                                  (* n_sent, padding *)
  hw_ift_bytes ++                                           (* if_name, if_index *)
  lbytes 4 64 ++ zeros 4.                                   (* n_if, padding *)

(* the model block (fuzz_link.c:286-295) after model_read *)
Definition rd_md : list byte :=
  lbytes 4 0 ++ lbytes 4 0 ++ lbytes 4 1 ++                 (* socket_errno send_errno next *)
  pad 512 (req_read 2) ++ zeros (15 * 512) ++ zeros 4 ++    (* req, padding *)
  lbytes 8 32 ++ zeros (15 * 8) ++                          (* req_len *)
  lbytes 4 1 ++                                             (* n_req *)
  zeros (32 * 16) ++                                        (* mark *)
  lbytes 4 0.                                               (* n_mark *)

(* text_buf(16), then reac_link_alias_read's NUL at [0] *)
Definition bs_kind : list byte := zb 0 :: repeat (zb 0x5a) 15.
Definition heap_sh : list byte :=
  map zb [0xfa; 0xfa; 0; 0; 1; 0xfa; 0xfa; 0xfa; 0; 0; 1; 0xfa; 0xfa; 0xfa; 0xfa; 0xfa].
Definition fr_sh : list byte :=
  map zb (repeat 0xf2 8 ++ repeat 0 5 ++ repeat 0xf2 5 ++ repeat 0 5 ++ repeat 0xf3 5).

Definition R_NLS : rg := RF S_NL 33999 0.
Definition R_NLR : rg := RF (S_NL + 33999) 1 0xf9.
Definition R_GN : rg := RL LA_G_NAMES 512 gn_bytes.
Definition R_GNS : rg := RF S_GN 64 0.
Definition R_ODD : rg := RL LA_ODD_STR 192 odd_bytes.
Definition R_ODDS : rg := RL S_ODD 24 odd_sh.
Definition R_KB : rg := RL HW_KB 17 (bs_kind ++ [zb GUARD_BYTE]).
Definition R_AB : rg := RL HW_AB 17 (bs_kind ++ [zb GUARD_BYTE]).
Definition R_HS : rg := RL S_HEAP 16 heap_sh.
Definition R_WK : rg := RF HW_WK 40 0.
Definition R_WA : rg := RF HW_WA 40 0.
Definition R_FS : rg := RL (S_F4 + 84) 28 fr_sh.
Definition R_MB : rg := RL HW_MB MD_SIZE rd_md.
Definition R_MBS : rg := RF S_MB 1107 0.
Definition R_MBR : rg := RF (S_MB + 1107) 5 0xfa.
Definition rd_rest : list rg :=
  [R_NLS; R_NLR; R_GN; R_GNS; R_ODD; R_ODDS; R_KB; R_AB; R_HS; R_WK; R_WA; R_FS; R_MB; R_MBS; R_MBR].
Definition rd_rgs (bs : list byte) : list rg := RL LA_G_NL NK_SIZE bs :: rd_rest.

(* the memory of run R, and the same without g_nl's bytes (what the closed checks run on) *)
Definition HW_M : word -> option byte := rmem (rd_rgs hw_bs).
Definition RD0 : word -> option byte := rmem (rd_rgs []).

(* ==========================================================================
   6. The g_nl list: ONE computation, then abstract lists only
   ========================================================================== *)

Definition hw_check (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? NK_SIZE) &&
  (nk_n_chunks bs =? 1) && (nk_next bs =? 1) && (nk_n_sent bs =? 1) && (nk_n_if bs =? 64) &&
  (nk_open bs =? 0) && (nk_opened bs =? 1) && (nk_closed bs =? 1) && (nk_misuse bs =? 0) &&
  (nk_end_errno bs =? 105) && (nk_socket_errno bs =? 0) && (nk_send_errno bs =? 0) &&
  (fld_u64 bs (NK_CHUNK_LEN + 8 * 0) =? 36) && (fld_u64 bs (NK_SENT_LEN + 8 * 0) =? 32) &&
  bl_eqb (nk_sent_one bs 0) (req_read 2) && bl_eqb (slice bs NK_IF_NAME 960) hw_ift_bytes.

Lemma hw_check_ok : hw_check hw_bs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hw_fields : forall bs, hw_check bs = true ->
  Z.of_nat (length bs) = NK_SIZE /\
  nk_n_chunks bs = 1 /\ nk_next bs = 1 /\ nk_n_sent bs = 1 /\ nk_n_if bs = 64 /\
  nk_open bs = 0 /\ nk_opened bs = 1 /\ nk_closed bs = 1 /\ nk_misuse bs = 0 /\
  nk_end_errno bs = 105 /\ nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  fld_u64 bs (NK_CHUNK_LEN + 8 * 0) = 36 /\ fld_u64 bs (NK_SENT_LEN + 8 * 0) = 32 /\
  nk_sent_one bs 0 = req_read 2 /\ slice bs NK_IF_NAME 960 = hw_ift_bytes.
Proof.
  intros bs H. unfold hw_check in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11] H12] H13] H14] H15] H16].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14.
  apply bl_eqb_eq in H15, H16.
  repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma hw_nlk_wf : forall bs, hw_check bs = true -> nlk_wf bs.
Proof.
  intros bs Hb.
  destruct (hw_fields bs Hb) as (_ & Hc & Hn & Hs & Hi & Ho & Hod & Hcl & Hm & He1 & He2 & He3 & Hl0 & Hs0 & _).
  unfold nlk_wf, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  - intros j Hj. assert (j = 0) by lia. subst j. lia.
  - intros j Hj. assert (j = 0) by lia. subst j. lia.
Qed.

(* the model block of run R, checked as a small closed list *)
Definition md_check (mbs : list byte) : bool :=
  (Z.of_nat (length mbs) =? MD_SIZE) && (md_n_req mbs =? 1) && (md_next mbs =? 1) &&
  (md_socket_errno mbs =? 0) && (md_send_errno mbs =? 0) && (md_n_mark mbs =? 0) &&
  (fld_u64 mbs (MD_REQ_LEN + 8 * 0) =? 32) && bl_eqb (md_req_one mbs 0) (req_read 2).

Lemma rd_md_ok : md_check rd_md = true.
Proof. vm_compute. reflexivity. Qed.

Lemma md_fields : forall mbs, md_check mbs = true ->
  Z.of_nat (length mbs) = MD_SIZE /\ md_n_req mbs = 1 /\ md_next mbs = 1 /\ md_socket_errno mbs = 0 /\
  md_send_errno mbs = 0 /\ md_n_mark mbs = 0 /\ fld_u64 mbs (MD_REQ_LEN + 8 * 0) = 32 /\
  md_req_one mbs 0 = req_read 2.
Proof.
  intros mbs H. unfold md_check in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[H1 H2] H3] H4] H5] H6] H7] H8].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6, H7. apply bl_eqb_eq in H8.
  repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma md_wf_of : forall mbs, md_check mbs = true -> model_wf mbs.
Proof.
  intros mbs Hm. destruct (md_fields mbs Hm) as (_ & Hn & Hx & Hs & Hd & Hk & H0 & _).
  unfold model_wf, model_marks_wf, slots_terminated, NL_SENT_MAX, NL_SENT_LEN, MARKS_MAX.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  - intros i Hi. assert (i = 0) by lia. subst i. lia.
Qed.

Lemma hw_requests : forall bs mbs, hw_check bs = true -> md_check mbs = true -> requests_are bs mbs.
Proof.
  intros bs mbs Hb Hm.
  destruct (hw_fields bs Hb) as (_ & _ & _ & Hs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs0 & Hq & _).
  destruct (md_fields mbs Hm) as (_ & Hn & _ & _ & _ & _ & Hm0 & Hmq).
  split; [lia|]. intros i Hi. assert (i = 0) by lia. subst i.
  split; [lia|]. rewrite Hq, Hmq. reflexivity.
Qed.

(* ==========================================================================
   7. The memory of run R
   ========================================================================== *)

Lemma rd_disj : forall bs, rgs_disj (rd_rgs bs) = true.
Proof. intros bs. vm_compute. reflexivity. Qed.

Lemma rd_ext : forall bs, mext RD0 (rmem (rd_rgs bs)).
Proof.
  intros bs w b H. unfold RD0, rmem, rd_rgs in *. cbn [rlook rg_lo rg_n rg_val] in *.
  revert H. destruct (inrz (bv_unsigned w) LA_G_NL NK_SIZE); intros H; [|exact H].
  rewrite nth_error_nil in H. discriminate.
Qed.

Lemma rd_at : forall bs i, (i < length bs)%nat -> Z.of_nat (length bs) = NK_SIZE ->
  rmem (rd_rgs bs) (Z_to_bv 64 (LA_G_NL + Z.of_nat i)) = nth_error bs i.
Proof.
  intros bs i Hi Hl. unfold rmem, rd_rgs. cbn [rlook rg_lo rg_n rg_val].
  rewrite unsigned_lit_small by (unfold LA_G_NL, NK_SIZE in *; lia).
  rewrite inrz_true by (unfold LA_G_NL, NK_SIZE in *; lia).
  replace (LA_G_NL + Z.of_nat i - LA_G_NL) with (Z.of_nat i) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma rd_anlk : forall segs bs, Z.of_nat (length bs) = NK_SIZE -> anlk_at segs (rmem (rd_rgs bs)) LA_G_NL bs.
Proof.
  intros segs bs Hlen. split; [|exact Hlen]. split.
  - split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL, NK_SIZE in *; lia|].
    intros i Hi. unfold mbyte. rewrite (rd_at bs i Hi Hlen).
    destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  - intros i Hi. unfold writable_at, wview.
    replace (LA_G_NL + i) with (LA_G_NL + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rd_at bs (Z.to_nat i) ltac:(lia) Hlen).
    destruct (nth_error bs (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|]. apply nth_error_None in E. lia.
Qed.

(* the n little-endian bytes of v at g_nl + off + o, from a slice of g_nl and a slice of it *)
Lemma rd_val : forall segs bs off W L o n v, Z.of_nat (length bs) = NK_SIZE ->
  0 <= off -> 0 <= o -> o + Z.of_nat n <= W -> off + W <= NK_SIZE ->
  slice bs off W = L -> slice L o (Z.of_nat n) = lbytes n v ->
  val_mem segs (rmem (rd_rgs bs)) (LA_G_NL + off + o) n v.
Proof.
  intros segs bs off W L o n v Hl Ho Hoo Hn HW HL Hs k Hk.
  assert (Hi : (Z.to_nat off + (Z.to_nat o + k) < length bs)%nat) by lia.
  replace (LA_G_NL + off + o + Z.of_nat k) with (LA_G_NL + Z.of_nat (Z.to_nat off + (Z.to_nat o + k))) by lia.
  unfold mbyte. rewrite (rd_at bs _ Hi Hl).
  rewrite <- (slice_nth bs off W (Z.to_nat o + k)) by lia. rewrite HL.
  rewrite <- (slice_nth L o (Z.of_nat n) k) by lia. rewrite Hs, (lbytes_nth n v k Hk). reflexivity.
Qed.

(* membership by position: `reflexivity` on `nth_error rs k = Some r` only computes the list's spine. (Never prove
   these by `left; reflexivity` along the list: unifying two RL regions compares their byte lists tail first, which
   backtracks without end on two different long lists.) *)
Lemma in_NLS : forall bs, In R_NLS (rd_rgs bs).
Proof. intros bs. right. apply (nth_error_In rd_rest 0). reflexivity. Qed.
Lemma in_MB : forall bs, In R_MB (rd_rgs bs).
Proof. intros bs. right. apply (nth_error_In rd_rest 12). reflexivity. Qed.
Lemma in_MBS : forall bs, In R_MBS (rd_rgs bs).
Proof. intros bs. right. apply (nth_error_In rd_rest 13). reflexivity. Qed.

(* ==========================================================================
   8. check_socket (LLVMFuzzerTestOneInput 0x836b0)
   ========================================================================== *)

Lemma check_socket_of : forall segs regs bs, hw_check bs = true -> check_socket_apre segs regs (rmem (rd_rgs bs)).
Proof.
  intros segs regs bs Hb. destruct (hw_fields bs Hb) as (Hlen & _ & _ & _ & _ & Ho & Hod & Hcl & Hm & _).
  exists bs. split; [exact (rd_anlk segs bs Hlen)|]. split; [exact Ho|]. split; [lia | exact Hm].
Qed.

(* the Pre lambda of check_socket_acontract holds at HW_M, for every segment list and register file *)
Lemma check_socket_apre_sat : forall segs (regs : bvmap 5 word), check_socket_apre segs regs HW_M.
Proof. intros segs regs. exact (check_socket_of segs regs hw_bs hw_check_ok). Qed.

(* ==========================================================================
   9. index_of (LLVMFuzzerTestOneInput 0x836d8, or model_read +0x17c) on g_names[0] = "nl0"
   ========================================================================== *)

(* per entry: its index in [0, 2^31), its string at its pointer, and the facts strcmp asks of that string *)
Definition ent_chk (m : word -> option byte) (e : Z * list byte * Z) : bool :=
  (0 <=? snd e) && (snd e <? 2 ^ 31) && cstr_chk m (fst (fst e)) (snd (fst e)) &&
  sarg_chk m HW_SP INDEX_OF_AK (fst (fst e)) (snd (fst e)).
Lemma ix_ok : forallb (ent_chk RD0) hw_ift = true.
Proof. vm_compute. reflexivity. Qed.

(* per entry: its pointer and its index in the 960 bytes of if_name / if_index *)
Definition ift_chk (j : nat) : bool :=
  match nth_error hw_ift j with
  | Some e => bl_eqb (slice hw_ift_bytes (8 * Z.of_nat j) 8) (lbytes 8 (fst (fst e))) &&
              bl_eqb (slice hw_ift_bytes (640 + 4 * Z.of_nat j) 4) (lbytes 4 (snd e))
  | None => false
  end.
Lemma ift_ok : forallb ift_chk (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hw_ift_len : length hw_ift = 64%nat.
Proof. reflexivity. Qed.
Lemma hw_tab_len : Z.of_nat (length hw_tab) = 64.
Proof. reflexivity. Qed.

(* THE SOUNDNESS LEMMA of the two checks: every entry of the table *)
Lemma hw_entry : forall segs regs bs j p s ix, hw_check bs = true -> spZ regs = HW_SP ->
  nth_error hw_ift j = Some (p, s, ix) ->
  (0 <= ix < 2 ^ 31) /\ p <> 0 /\ 0 <= p < 2 ^ 64 /\
  au64_at segs (rmem (rd_rgs bs)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) p /\
  au32_at segs (rmem (rd_rgs bs)) (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat j) ix /\
  acstr_at segs (rmem (rd_rgs bs)) p s /\ astrcmp_arg segs regs INDEX_OF_AK (rmem (rd_rgs bs)) p s.
Proof.
  intros segs regs bs j p s ix Hb Hsp Hj.
  destruct (hw_fields bs Hb) as (Hlen & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hift).
  assert (Hj64 : (j < 64)%nat) by (rewrite <- hw_ift_len; apply nth_error_Some; rewrite Hj; discriminate).
  pose proof ix_ok as E. rewrite forallb_forall in E. specialize (E _ (nth_error_In _ _ Hj)).
  unfold ent_chk in E. cbn [fst snd] in E. repeat rewrite andb_true_iff in E.
  destruct E as [[[E1 E2] E3] E4]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  pose proof (acstr_chk segs RD0 _ p s (rd_ext bs) E3) as Hc.
  pose proof (sarg_chk_ok segs regs RD0 _ HW_SP INDEX_OF_AK p s (rd_ext bs) Hsp E4) as Ha.
  pose proof E3 as E3'. unfold cstr_chk in E3'. repeat rewrite andb_true_iff in E3'.
  destruct E3' as [[[Q0 Q1] _] _]. apply Z.leb_le in Q0, Q1.
  pose proof (proj1 Ha) as Hpos.
  pose proof ift_ok as F. rewrite forallb_forall in F. specialize (F j ltac:(apply in_seq; lia)).
  unfold ift_chk in F. rewrite Hj in F. cbn [fst snd] in F. apply andb_prop in F as [F1 F2].
  apply bl_eqb_eq in F1, F2.
  split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold au64_at.
    apply (rd_val segs bs NK_IF_NAME 960 hw_ift_bytes (8 * Z.of_nat j) 8 p Hlen);
      [unfold NK_IF_NAME; lia | lia | lia | unfold NK_IF_NAME, NK_SIZE; lia | exact Hift | exact F1]. }
  split.
  { unfold au32_at.
    replace (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat j) with (LA_G_NL + NK_IF_NAME + (640 + 4 * Z.of_nat j))
      by (unfold NK_IF_INDEX, NK_IF_NAME; lia).
    apply (rd_val segs bs NK_IF_NAME 960 hw_ift_bytes (640 + 4 * Z.of_nat j) 4 ix Hlen);
      [unfold NK_IF_NAME; lia | lia | lia | unfold NK_IF_NAME, NK_SIZE; lia | exact Hift | exact F2]. }
  split; [exact Hc | exact Ha].
Qed.

Lemma hw_tab_ift : forall i nm ix, nth_error hw_tab i = Some (nm, ix) -> exists p, nth_error hw_ift i = Some (p, nm, ix).
Proof.
  intros i nm ix H. rewrite nth_error_map in H.
  destruct (nth_error hw_ift i) as [[[p s] x]|]; cbn in H; [|discriminate]. injection H as <- <-.
  exists p. reflexivity.
Qed.

Lemma hw_iftab : forall segs regs bs, hw_check bs = true -> spZ regs = HW_SP ->
  aiftab_at segs (rmem (rd_rgs bs)) LA_G_NL bs hw_tab.
Proof.
  intros segs regs bs Hb Hsp. destruct (hw_fields bs Hb) as (_ & _ & _ & _ & Hnif & _).
  split; [rewrite hw_tab_len; exact Hnif|]. split; [rewrite hw_tab_len; zle|].
  intros i nm ix Hi. destruct (hw_tab_ift i nm ix Hi) as [p Hp].
  destruct (hw_entry segs regs bs i p nm ix Hb Hsp Hp) as (Hix & Hp0 & _ & Hw & Hx & Hc & _).
  split; [exact Hix|]. exists p. split; [exact Hw|]. split; [exact Hp0|]. split; [exact Hc | exact Hx].
Qed.

Lemma index_of_of : forall segs regs bs, hw_check bs = true -> aarg regs 0 = LA_G_NAMES -> spZ regs = HW_SP ->
  index_of_apre segs regs (rmem (rd_rgs bs)).
Proof.
  intros segs regs bs Hb H0 Hsp. destruct (hw_fields bs Hb) as (Hlen & _).
  assert (E0 : nth_error hw_ift 0 = Some (LA_G_NAMES, nl_name 0, 2)) by reflexivity.
  destruct (hw_entry segs regs bs 0 LA_G_NAMES (nl_name 0) 2 Hb Hsp E0) as (_ & _ & _ & _ & _ & Hc & Ha).
  unfold index_of_apre. rewrite H0. exists bs, hw_tab, (nl_name 0).
  split; [exact (rd_anlk segs bs Hlen)|].
  split; [exact (hw_iftab segs regs bs Hb Hsp)|].
  rewrite hw_tab_len.
  split.
  { apply (ra_fill segs (rd_rgs bs) _ S_NL 33999);
      [apply mext_refl | apply rd_disj | apply in_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_NAME) (8 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split.
  { apply (ra_fill segs (rd_rgs bs) _ S_NL 33999);
      [apply mext_refl | apply rd_disj | apply in_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_INDEX) (4 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split; [unfold LA_G_NAMES; discriminate|].
  split; [exact Hc|]. split; [exact Ha|].
  intros i n2 ix q Hi Hq Hqr. destruct (hw_tab_ift i n2 ix Hi) as [p Hp].
  destruct (hw_entry segs regs bs i p n2 ix Hb Hsp Hp) as (_ & _ & Hpr & Hw & _ & _ & Hpa).
  rewrite (val_mem8_inj segs _ _ q p Hq Hw Hqr Hpr). exact Hpa.
Qed.

(* the Pre lambda of index_of_acontract holds at HW_M, for every segment list, at every register file with
   a0 = &g_names[0] ("nl0") and sp = HW_SP *)
Lemma index_of_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = LA_G_NAMES -> spZ regs = HW_SP -> index_of_apre segs regs HW_M.
Proof. intros segs regs H0 Hsp. exact (index_of_of segs regs hw_bs hw_check_ok H0 Hsp). Qed.

(* ==========================================================================
   10. check_bounds (LLVMFuzzerTestOneInput 0x836fc) on the kind buffer
   ========================================================================== *)

Lemma cb_ok : bytes_chk RD0 HW_KB (bs_kind ++ [zb GUARD_BYTE]) = true /\ ra_chk RD0 HW_KB 17 = true /\
  hull_chk RD0 HW_KB 16 = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

Lemma tb_len : length (bs_kind ++ [zb GUARD_BYTE]) = 17%nat.
Proof. reflexivity. Qed.

Lemma check_bounds_of : forall segs regs bs, aarg regs 0 = HW_KB -> aarg regs 1 = 16 -> spZ regs = HW_SP ->
  check_bounds_apre segs regs (rmem (rd_rgs bs)).
Proof.
  intros segs regs bs H0 H1 Hsp. destruct cb_ok as (Cb & Cr & Ch).
  unfold check_bounds_apre. rewrite H0, H1. exists bs_kind.
  split; [unfold HW_KB; discriminate|].
  split; [split; [zle | zlt]|].
  split.
  { split; [|reflexivity].
    apply (au8arr_chk segs RD0 _ HW_KB _ (rd_ext bs) Cb); zle. }
  split; [left; reflexivity|].
  split; [unfold amem_range; right; split; zle|].
  split; [exact (ra_chk_ok segs RD0 _ _ _ (rd_ext bs) Cr)|].
  split; [exact (hull_chk_ok segs RD0 _ _ _ (rd_ext bs) Ch)|].
  unfold apart_frame. rewrite Hsp. left. zle.
Qed.

(* the Pre lambda of check_bounds_acontract holds at HW_M, for every segment list, at every register file with
   a0 = HW_KB, a1 = 16 and sp = HW_SP *)
Lemma check_bounds_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = HW_KB -> aarg regs 1 = 16 -> spZ regs = HW_SP -> check_bounds_apre segs regs HW_M.
Proof. intros segs regs H0 H1 Hsp. exact (check_bounds_of segs regs hw_bs H0 H1 Hsp). Qed.

(* ==========================================================================
   11. check_read (op_read): rc = want = 0, four empty strings
   ========================================================================== *)

Definition cr_ptrs : list Z := [HW_KB; HW_WK; HW_AB; HW_WA].
Lemma cr_all : forallb (fun p => cstr_chk RD0 p [] && sarg_chk RD0 HW_SP CHECK_READ_AK p []) cr_ptrs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cr_one : forall segs regs bs p, spZ regs = HW_SP -> In p cr_ptrs ->
  acstr_at segs (rmem (rd_rgs bs)) p [] /\ astrcmp_arg segs regs CHECK_READ_AK (rmem (rd_rgs bs)) p [].
Proof.
  intros segs regs bs p Hsp Hin. pose proof cr_all as C. rewrite forallb_forall in C.
  pose proof (C p Hin) as Cp. apply andb_prop in Cp as [C1 C2]. split.
  - exact (acstr_chk segs RD0 _ p [] (rd_ext bs) C1).
  - exact (sarg_chk_ok segs regs RD0 _ HW_SP CHECK_READ_AK p [] (rd_ext bs) Hsp C2).
Qed.

Lemma check_read_of : forall segs regs bs, getr regs 10 = w64 0 -> getr regs 11 = w64 0 ->
  aarg regs 2 = HW_KB -> aarg regs 3 = HW_WK -> aarg regs 4 = HW_AB -> aarg regs 5 = HW_WA ->
  spZ regs = HW_SP -> check_read_apre segs regs (rmem (rd_rgs bs)).
Proof.
  intros segs regs bs H10 H11 H2 H3 H4 H5 Hsp. unfold check_read_apre.
  split; [intros E; rewrite H11 in E; exfalso; exact (w64_0_ne E)|].
  split; [intros _; rewrite H10, H11; reflexivity|].
  intros _. exists [], [], [], []. rewrite H2, H3, H4, H5.
  destruct (cr_one segs regs bs HW_KB Hsp ltac:(apply (nth_error_In cr_ptrs 0); reflexivity)) as [Ck Ak].
  destruct (cr_one segs regs bs HW_WK Hsp ltac:(apply (nth_error_In cr_ptrs 1); reflexivity)) as [Cwk Awk].
  destruct (cr_one segs regs bs HW_AB Hsp ltac:(apply (nth_error_In cr_ptrs 2); reflexivity)) as [Ca Aa].
  destruct (cr_one segs regs bs HW_WA Hsp ltac:(apply (nth_error_In cr_ptrs 3); reflexivity)) as [Cwa Awa].
  split; [exact Ck|]. split; [exact Cwk|]. split; [exact Ca|]. split; [exact Cwa|].
  split; [exact Ak|]. split; [exact Awk|]. split; [exact Aa|]. split; [exact Awa|].
  split; reflexivity.
Qed.

(* the Pre lambda of check_read_acontract holds at HW_M, for every segment list, at every register file with
   a0 = a1 = 0, a2 = HW_KB, a3 = HW_WK, a4 = HW_AB, a5 = HW_WA and sp = HW_SP *)
Lemma check_read_apre_sat : forall segs (regs : bvmap 5 word),
  getr regs 10 = w64 0 -> getr regs 11 = w64 0 ->
  aarg regs 2 = HW_KB -> aarg regs 3 = HW_WK -> aarg regs 4 = HW_AB -> aarg regs 5 = HW_WA ->
  spZ regs = HW_SP -> check_read_apre segs regs HW_M.
Proof.
  intros segs regs H10 H11 H2 H3 H4 H5 Hsp. exact (check_read_of segs regs hw_bs H10 H11 H2 H3 H4 H5 Hsp).
Qed.

(* ==========================================================================
   12. check_requests (op_read, after check_read)
   ========================================================================== *)

Lemma cq_ok : hull_chk RD0 LA_G_NL NK_SIZE = true /\ hull_chk RD0 HW_MB MD_SIZE = true.
Proof. split; vm_compute; reflexivity. Qed.

Lemma check_requests_of : forall segs regs bs, hw_check bs = true -> aarg regs 0 = HW_MB -> spZ regs = HW_SP ->
  check_requests_apre segs regs (rmem (rd_rgs bs)).
Proof.
  intros segs regs bs Hb H0 Hsp. destruct (hw_fields bs Hb) as (Hlen & _).
  destruct (md_fields rd_md rd_md_ok) as (Hml & _). destruct cq_ok as [Q1 Q2].
  unfold check_requests_apre. rewrite H0. exists bs, rd_md.
  split; [exact (rd_anlk segs bs Hlen)|].
  split.
  { split; [|exact Hml].
    apply (rl_au8arr segs (rd_rgs bs) _ HW_MB MD_SIZE);
      [apply mext_refl | apply rd_disj | apply in_MB | exact Hml | zle | zle]. }
  split; [exact (hw_nlk_wf bs Hb)|].
  split; [exact (md_wf_of rd_md rd_md_ok)|].
  split; [exact (hw_requests bs rd_md Hb rd_md_ok)|].
  split.
  { apply (ra_fill segs (rd_rgs bs) _ S_MB 1107);
      [apply mext_refl | apply rd_disj | apply in_MBS | zle | zle |].
    intros x Hx. apply (shadow_win HW_MB MD_SIZE); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs RD0 _ _ _ (rd_ext bs) Q2)|].
  split; [unfold amem_range; right; split; zle|].
  split.
  { apply (ra_fill segs (rd_rgs bs) _ S_NL 33999);
      [apply mext_refl | apply rd_disj | apply in_NLS | zle | zle |].
    intros x Hx. apply (shadow_win LA_G_NL NK_SIZE); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs RD0 _ _ _ (rd_ext bs) Q1)|].
  split.
  { unfold apart_frame. rewrite Hsp. left. zle. }
  unfold apart_gnl. right. zle.
Qed.

(* the Pre lambda of check_requests_acontract holds at HW_M, for every segment list, at every register file with
   a0 = HW_MB (the model block) and sp = HW_SP *)
Lemma check_requests_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = HW_MB -> spZ regs = HW_SP -> check_requests_apre segs regs HW_M.
Proof. intros segs regs H0 Hsp. exact (check_requests_of segs regs hw_bs hw_check_ok H0 Hsp). Qed.

(* ==========================================================================
   13. check_marks (op_mark of "nl0"): run M
   ========================================================================== *)

(* struct reac_served_marks after the mark: n = 1, name[0] = "nl0" *)
Definition mk_bs : list byte := lbytes 4 1 ++ pad 16 (nl_name 0) ++ zeros (31 * 16).
(* the model block after model_mark *)
Definition mk_md : list byte :=
  lbytes 4 0 ++ lbytes 4 0 ++ lbytes 4 2 ++                                     (* socket send next *)
  pad 512 (req_read 2) ++ pad 512 (req_write 2 S_SERVED) ++ zeros (14 * 512) ++ zeros 4 ++   (* req *)
  lbytes 8 32 ++ lbytes 8 52 ++ zeros (14 * 8) ++                               (* req_len *)
  lbytes 4 2 ++                                                                 (* n_req *)
  pad 16 (nl_name 0) ++ zeros (31 * 16) ++                                      (* mark *)
  lbytes 4 1.                                                                   (* n_mark *)
Definition mk_sh : list byte := repeat (zb 0) 64 ++ map zb [4; 0xfa; 0xfa; 0xfa; 0xfa; 0xfa; 0xfa; 0xfa].

Definition R_MK : rg := RL HW_MKB MK_SIZE mk_bs.
Definition R_MKS : rg := RL S_MKB 72 mk_sh.
Definition R_MB2 : rg := RL HW_MB MD_SIZE mk_md.
(* the marks block's chunk tail: calloc(1, 516) ends 4 bytes into a granule; the chunk's bytes [516, 520) are
   present (0, never written) *)
Definition R_MKT : rg := RF (HW_MKB + MK_SIZE) 4 0.
Definition mk_rgs : list rg := [R_MK; R_MKS; R_MB2; R_MBS; R_MBR; R_MKT].
Definition MK_M : word -> option byte := rmem mk_rgs.

Lemma mk_disj : rgs_disj mk_rgs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma in_mk_MK : In R_MK mk_rgs.
Proof. apply (nth_error_In mk_rgs 0). reflexivity. Qed.
Lemma in_mk_MB : In R_MB2 mk_rgs.
Proof. apply (nth_error_In mk_rgs 2). reflexivity. Qed.
Lemma in_mk_MBS : In R_MBS mk_rgs.
Proof. apply (nth_error_In mk_rgs 3). reflexivity. Qed.

Definition mk_check (gbs mbs : list byte) : bool :=
  (Z.of_nat (length gbs) =? MK_SIZE) && (Z.of_nat (length mbs) =? MD_SIZE) &&
  (mk_n gbs =? 1) && (md_n_mark mbs =? 1) &&
  Nat.ltb (nul_at (slice gbs (MK_NAME + MARK_LEN * 0) MARK_LEN)) (Z.to_nat MARK_LEN) &&
  Nat.ltb (nul_at (slice mbs (MD_MARK + MARK_LEN * 0) MARK_LEN)) (Z.to_nat MARK_LEN) &&
  bll_eqb (mk_names gbs) (md_marks mbs).

Lemma mk_check_ok : mk_check mk_bs mk_md = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mk_fields : forall gbs mbs, mk_check gbs mbs = true ->
  Z.of_nat (length gbs) = MK_SIZE /\ Z.of_nat (length mbs) = MD_SIZE /\ mk_n gbs = 1 /\ md_n_mark mbs = 1 /\
  (nul_at (slice gbs (MK_NAME + MARK_LEN * 0) MARK_LEN) < Z.to_nat MARK_LEN)%nat /\
  (nul_at (slice mbs (MD_MARK + MARK_LEN * 0) MARK_LEN) < Z.to_nat MARK_LEN)%nat /\
  mk_names gbs = md_marks mbs.
Proof.
  intros gbs mbs H. unfold mk_check in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  apply Z.eqb_eq in H1, H2, H3, H4. apply Nat.ltb_lt in H5, H6. apply bll_eqb_eq in H7.
  repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma km_ok : ra_chk MK_M HW_MKB MK_SIZE = true /\ hull_chk MK_M HW_MKB MK_SIZE = true /\
  hull_chk MK_M HW_MB MD_SIZE = true /\ pres_chk MK_M (HW_MKB + MK_SIZE) ((HW_MKB + MK_SIZE + 7) / 8 * 8) = true /\
  pres_chk MK_M (HW_MB + MD_SIZE) ((HW_MB + MD_SIZE + 7) / 8 * 8) = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

(* the Pre lambda of check_marks_acontract holds at MK_M, for every segment list, at every register file with
   a0 = HW_MKB (the marks block), a1 = HW_MB (the model block) and sp = HW_SP *)
Lemma check_marks_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = HW_MKB -> aarg regs 1 = HW_MB -> spZ regs = HW_SP -> check_marks_apre segs regs MK_M.
Proof.
  intros segs regs H0 H1 Hsp.
  destruct (mk_fields mk_bs mk_md mk_check_ok) as (Hgl & Hml & Hgn & Hmn & Hgt & Hmt & Hna).
  destruct km_ok as (K1 & K2 & K3 & K4 & K5).
  unfold check_marks_apre. rewrite H0, H1. exists mk_bs, mk_md.
  split.
  { split; [|exact Hgl].
    apply (rl_au8arr segs mk_rgs _ HW_MKB MK_SIZE);
      [apply mext_refl | exact mk_disj | exact in_mk_MK | exact Hgl | zle | zle]. }
  split.
  { split; [|exact Hml].
    apply (rl_au8arr segs mk_rgs _ HW_MB MD_SIZE);
      [apply mext_refl | exact mk_disj | exact in_mk_MB | exact Hml | zle | zle]. }
  split.
  { unfold marks_wf. rewrite Hgn. split; [split; zle|]. unfold slots_terminated. intros i Hi.
    assert (i = 0) by (clear - Hi; lia). subst i. exact Hgt. }
  split.
  { unfold model_marks_wf. rewrite Hmn. split; [split; zle|]. unfold slots_terminated. intros i Hi.
    assert (i = 0) by (clear - Hi; lia). subst i. exact Hmt. }
  split; [split; [rewrite Hgn, Hmn; reflexivity | exact Hna]|].
  split; [exact (ra_chk_ok segs MK_M _ _ _ (mext_refl _) K1)|].
  split; [exact (hull_chk_ok segs MK_M _ _ _ (mext_refl _) K2)|].
  split; [unfold amem_range; right; split; zle|].
  split.
  { apply (ra_fill segs mk_rgs _ S_MB 1107);
      [apply mext_refl | exact mk_disj | exact in_mk_MBS | zle | zle |].
    intros x Hx. apply (shadow_win HW_MB MD_SIZE); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs MK_M _ _ _ (mext_refl _) K3)|].
  split; [unfold amem_range; right; split; zle|].
  split.
  { unfold apart_frame. rewrite Hsp. left. zle. }
  split; [unfold apart_frame; rewrite Hsp; left; zle|].
  split; [exact (pres_chk_ok segs MK_M MK_M _ _ (mext_refl _) K4)|].
  (* the model block ends on a granule boundary: the range is empty *)
  exact (pres_chk_ok segs MK_M MK_M _ _ (mext_refl _) K5).
Qed.

(* ==========================================================================
   15. The same machinery for any region list headed by g_nl (runs R0 and W)
   ========================================================================== *)

Lemma gl_ext : forall bs rest, mext (rmem (RL LA_G_NL NK_SIZE [] :: rest)) (rmem (RL LA_G_NL NK_SIZE bs :: rest)).
Proof.
  intros bs rest w b H. unfold rmem in *. cbn [rlook rg_lo rg_n rg_val] in *.
  revert H. destruct (inrz (bv_unsigned w) LA_G_NL NK_SIZE); intros H; [|exact H].
  rewrite nth_error_nil in H. discriminate.
Qed.

Lemma gl_at : forall bs rest i, (i < length bs)%nat -> Z.of_nat (length bs) = NK_SIZE ->
  rmem (RL LA_G_NL NK_SIZE bs :: rest) (Z_to_bv 64 (LA_G_NL + Z.of_nat i)) = nth_error bs i.
Proof.
  intros bs rest i Hi Hl. unfold rmem. cbn [rlook rg_lo rg_n rg_val].
  rewrite unsigned_lit_small by (unfold LA_G_NL, NK_SIZE in *; lia).
  rewrite inrz_true by (unfold LA_G_NL, NK_SIZE in *; lia).
  replace (LA_G_NL + Z.of_nat i - LA_G_NL) with (Z.of_nat i) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma gl_anlk : forall segs bs rest, Z.of_nat (length bs) = NK_SIZE ->
  anlk_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) LA_G_NL bs.
Proof.
  intros segs bs rest Hlen. split; [|exact Hlen]. split.
  - split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL, NK_SIZE in *; lia|].
    intros i Hi. unfold mbyte. rewrite (gl_at bs rest i Hi Hlen).
    destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  - intros i Hi. unfold writable_at, wview.
    replace (LA_G_NL + i) with (LA_G_NL + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (gl_at bs rest (Z.to_nat i) ltac:(lia) Hlen).
    destruct (nth_error bs (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|]. apply nth_error_None in E. lia.
Qed.

Lemma gl_val : forall segs bs rest off W L o n v, Z.of_nat (length bs) = NK_SIZE ->
  0 <= off -> 0 <= o -> o + Z.of_nat n <= W -> off + W <= NK_SIZE ->
  slice bs off W = L -> slice L o (Z.of_nat n) = lbytes n v ->
  val_mem segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) (LA_G_NL + off + o) n v.
Proof.
  intros segs bs rest off W L o n v Hl Ho Hoo Hn HW HL Hs k Hk.
  assert (Hi : (Z.to_nat off + (Z.to_nat o + k) < length bs)%nat) by lia.
  replace (LA_G_NL + off + o + Z.of_nat k) with (LA_G_NL + Z.of_nat (Z.to_nat off + (Z.to_nat o + k))) by lia.
  unfold mbyte. rewrite (gl_at bs rest _ Hi Hl).
  rewrite <- (slice_nth bs off W (Z.to_nat o + k)) by lia. rewrite HL.
  rewrite <- (slice_nth L o (Z.of_nat n) k) by lia. rewrite Hs, (lbytes_nth n v k Hk). reflexivity.
Qed.

(* eight bytes fix a value modulo 2^64 *)
Lemma val_mem8_mod : forall segs m a p q, val_mem segs m a 8 p -> val_mem segs m a 8 q ->
  0 <= q < 2 ^ 64 -> p mod 2 ^ 64 = q.
Proof.
  intros segs m a p q Hp Hq Hqr. apply le_byte8_inj; [| apply Z.mod_pos_bound; lia | exact Hqr].
  intros k Hk.
  assert (E : YO0f.le_byte (p mod 2 ^ 64) 8 k = YO0f.le_byte p 8 k)
    by (unfold YO0f.le_byte; change (8 * Z.of_nat 8) with 64; rewrite Z.mod_mod by lia; reflexivity).
  rewrite E. specialize (Hp k Hk). specialize (Hq k Hk). rewrite Hp in Hq.
  assert (E2 : bv_unsigned (Z_to_bv 8 (YO0f.le_byte p 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte q 8 k)))
    by congruence.
  rewrite !Z_to_bv_unsigned in E2. unfold bv_wrap in E2. change (bv_modulus 8) with 256 in E2.
  rewrite !Z.mod_small in E2 by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia). exact E2.
Qed.

(* a range apart from [q, q + n) is apart from [p, p + n) for every p with p mod 2^64 = q *)
Lemma apart_mod64 : forall a k p q n, p mod 2 ^ 64 = q -> 0 <= q -> q + n <= 2 ^ 64 -> 0 <= n ->
  0 <= a -> a + k <= 2 ^ 64 -> apart a k q n -> apart a k p n.
Proof.
  intros a k p q n Hm Hq Hqn Hn Ha Hak Hap. unfold apart in *.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as E. rewrite Hm in E.
  remember (p / 2 ^ 64) as t eqn:Ht. clear Ht.
  destruct (Z.lt_trichotomy t 0) as [T|[T|T]].
  - right. lia.
  - subst t. rewrite Z.mul_0_r, Z.add_0_l in E. subst p. exact Hap.
  - left. lia.
Qed.

(* per entry: as ent_chk, at a stack pointer sp and a stack bound K *)
Definition entk_chk (m : word -> option byte) (sp K : Z) (e : Z * list byte * Z) : bool :=
  (0 <=? snd e) && (snd e <? 2 ^ 31) && cstr_chk m (fst (fst e)) (snd (fst e)) &&
  sarg_chk m sp K (fst (fst e)) (snd (fst e)).

(* every table string lies outside [a, a + k). An abbreviation, as hw_tab: as a constant, `unfold tab_apartb in H`
   made gl_tab_apart's Qed run past a minute (the kernel evaluated forallb over the table). *)
Abbreviation tab_apartb a k :=
  (forallb (fun e : Z * list byte * Z =>
    (a + k <=? fst (fst e)) || (fst (fst e) + (Z.of_nat (length (snd (fst e))) + 1) <=? a)) hw_ift).

(* THE SOUNDNESS LEMMA of the entry checks, for any region list headed by g_nl *)
Lemma gl_entry : forall segs regs bs rest sp K j p s ix,
  Z.of_nat (length bs) = NK_SIZE -> slice bs NK_IF_NAME 960 = hw_ift_bytes -> spZ regs = sp ->
  forallb (entk_chk (rmem (RL LA_G_NL NK_SIZE [] :: rest)) sp K) hw_ift = true ->
  nth_error hw_ift j = Some (p, s, ix) ->
  (0 <= ix < 2 ^ 31) /\ p <> 0 /\ 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64 /\
  au64_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) p /\
  au32_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat j) ix /\
  acstr_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) p s /\
  astrcmp_arg segs regs K (rmem (RL LA_G_NL NK_SIZE bs :: rest)) p s.
Proof.
  intros segs regs bs rest sp K j p s ix Hlen Hift Hsp Hall Hj.
  assert (Hj64 : (j < 64)%nat) by (rewrite <- hw_ift_len; apply nth_error_Some; rewrite Hj; discriminate).
  pose proof Hall as E. rewrite forallb_forall in E. specialize (E _ (nth_error_In _ _ Hj)).
  unfold entk_chk in E. cbn [fst snd] in E. repeat rewrite andb_true_iff in E.
  destruct E as [[[E1 E2] E3] E4]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  pose proof (acstr_chk segs _ _ p s (gl_ext bs rest) E3) as Hc.
  pose proof (sarg_chk_ok segs regs _ _ sp K p s (gl_ext bs rest) Hsp E4) as Ha.
  pose proof E3 as E3'. unfold cstr_chk in E3'. repeat rewrite andb_true_iff in E3'.
  destruct E3' as [[[Q0 Q1] _] _]. apply Z.leb_le in Q0, Q1.
  pose proof (proj1 Ha) as Hpos.
  pose proof ift_ok as F. rewrite forallb_forall in F. specialize (F j ltac:(apply in_seq; lia)).
  unfold ift_chk in F. rewrite Hj in F. cbn [fst snd] in F. apply andb_prop in F as [F1 F2].
  apply bl_eqb_eq in F1, F2.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split.
  { unfold au64_at.
    apply (gl_val segs bs rest NK_IF_NAME 960 hw_ift_bytes (8 * Z.of_nat j) 8 p Hlen);
      [unfold NK_IF_NAME; lia | lia | lia | unfold NK_IF_NAME, NK_SIZE; lia | exact Hift | exact F1]. }
  split.
  { unfold au32_at.
    replace (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat j) with (LA_G_NL + NK_IF_NAME + (640 + 4 * Z.of_nat j))
      by (unfold NK_IF_INDEX, NK_IF_NAME; lia).
    apply (gl_val segs bs rest NK_IF_NAME 960 hw_ift_bytes (640 + 4 * Z.of_nat j) 4 ix Hlen);
      [unfold NK_IF_NAME; lia | lia | lia | unfold NK_IF_NAME, NK_SIZE; lia | exact Hift | exact F2]. }
  split; [exact Hc | exact Ha].
Qed.

Lemma gl_iftab : forall segs regs bs rest sp K, Z.of_nat (length bs) = NK_SIZE -> nk_n_if bs = 64 ->
  slice bs NK_IF_NAME 960 = hw_ift_bytes -> spZ regs = sp ->
  forallb (entk_chk (rmem (RL LA_G_NL NK_SIZE [] :: rest)) sp K) hw_ift = true ->
  aiftab_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) LA_G_NL bs hw_tab.
Proof.
  intros segs regs bs rest sp K Hlen Hnif Hift Hsp Hall.
  split; [rewrite hw_tab_len; exact Hnif|]. split; [rewrite hw_tab_len; lia|].
  intros i nm ix Hi. destruct (hw_tab_ift i nm ix Hi) as [p Hp].
  destruct (gl_entry segs regs bs rest sp K i p nm ix Hlen Hift Hsp Hall Hp) as (Hix & Hp0 & _ & _ & Hw & Hx & Hc & _).
  split; [exact Hix|]. exists p. split; [exact Hw|]. split; [exact Hp0|]. split; [exact Hc | exact Hx].
Qed.

Lemma gl_tabstr : forall segs regs bs rest sp K, Z.of_nat (length bs) = NK_SIZE ->
  slice bs NK_IF_NAME 960 = hw_ift_bytes -> spZ regs = sp ->
  forallb (entk_chk (rmem (RL LA_G_NL NK_SIZE [] :: rest)) sp K) hw_ift = true ->
  forall i n2 ix p, nth_error hw_tab i = Some (n2, ix) ->
    au64_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    0 <= p < 2 ^ 64 -> astrcmp_arg segs regs K (rmem (RL LA_G_NL NK_SIZE bs :: rest)) p n2.
Proof.
  intros segs regs bs rest sp K Hlen Hift Hsp Hall i n2 ix q Hi Hq Hqr.
  destruct (hw_tab_ift i n2 ix Hi) as [p Hp].
  destruct (gl_entry segs regs bs rest sp K i p n2 ix Hlen Hift Hsp Hall Hp) as (_ & _ & Hp0 & Hp1 & Hw & _ & _ & Ha).
  rewrite (val_mem8_inj segs _ _ q p Hq Hw Hqr ltac:(lia)). exact Ha.
Qed.

Lemma gl_tab_apart : forall segs regs bs rest sp K a k, Z.of_nat (length bs) = NK_SIZE ->
  slice bs NK_IF_NAME 960 = hw_ift_bytes -> spZ regs = sp ->
  forallb (entk_chk (rmem (RL LA_G_NL NK_SIZE [] :: rest)) sp K) hw_ift = true ->
  tab_apartb a k = true -> 0 <= a -> a + k <= 2 ^ 64 ->
  forall i n2 ix p, nth_error hw_tab i = Some (n2, ix) ->
    au64_at segs (rmem (RL LA_G_NL NK_SIZE bs :: rest)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    apart a k p (Z.of_nat (length n2) + 1).
Proof.
  intros segs regs bs rest sp K a k Hlen Hift Hsp Hall Hab Ha0 Hak i n2 ix q Hi Hq.
  destruct (hw_tab_ift i n2 ix Hi) as [p Hp].
  destruct (gl_entry segs regs bs rest sp K i p n2 ix Hlen Hift Hsp Hall Hp) as (_ & _ & Hp0 & Hp1 & Hw & _ & _ & _).
  rewrite forallb_forall in Hab. specialize (Hab _ (nth_error_In _ _ Hp)).
  cbn [fst snd] in Hab.
  apply (apart_mod64 a k q p (Z.of_nat (length n2) + 1));
    [exact (val_mem8_mod segs _ _ q p Hq Hw ltac:(lia)) | lia | lia | lia | exact Ha0 | exact Hak |].
  unfold apart. apply orb_prop in Hab as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* g_nl before the library call: kernel() queued the ACK chunk, model_begin cleared n_sent, no socket yet *)
Definition pr_bs : list byte :=
  ack36 ++ zeros (NL_CHUNKS * NL_CHUNK_MAX - 36) ++                         (* chunk *)
  lbytes 8 36 ++ zeros (8 * 63) ++                                          (* chunk_len *)
  lbytes 4 1 ++ lbytes 4 0 ++ lbytes 4 105 ++ lbytes 4 0 ++ lbytes 4 0 ++   (* n_chunks next end socket send *)
  lbytes 4 0 ++ lbytes 4 0 ++ lbytes 4 0 ++ lbytes 4 0 ++                   (* open opened closed misuse *)
  zeros (NL_SENT_MAX * NL_SENT_LEN) ++ zeros 4 ++                           (* sent, padding *)
  zeros (8 * 16) ++                                                         (* sent_len *)
  lbytes 4 0 ++ zeros 4 ++                                                  (* n_sent, padding *)
  hw_ift_bytes ++                                                           (* if_name, if_index *)
  lbytes 4 64 ++ zeros 4.                                                   (* n_if, padding *)
(* the model block after model_begin, first op: all 0 *)
Definition pr_md : list byte := zeros MD_SIZE.

Definition pr_check (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? NK_SIZE) &&
  (nk_n_chunks bs =? 1) && (nk_next bs =? 0) && (nk_n_sent bs =? 0) && (nk_n_if bs =? 64) &&
  (nk_open bs =? 0) && (nk_opened bs =? 0) && (nk_closed bs =? 0) && (nk_misuse bs =? 0) &&
  (nk_end_errno bs =? 105) && (nk_socket_errno bs =? 0) && (nk_send_errno bs =? 0) &&
  (fld_u64 bs (NK_CHUNK_LEN + 8 * 0) =? 36) && bl_eqb (slice bs NK_IF_NAME 960) hw_ift_bytes.

Lemma pr_check_ok : pr_check pr_bs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_fields : forall bs, pr_check bs = true ->
  Z.of_nat (length bs) = NK_SIZE /\
  nk_n_chunks bs = 1 /\ nk_next bs = 0 /\ nk_n_sent bs = 0 /\ nk_n_if bs = 64 /\
  nk_open bs = 0 /\ nk_opened bs = 0 /\ nk_closed bs = 0 /\ nk_misuse bs = 0 /\
  nk_end_errno bs = 105 /\ nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  fld_u64 bs (NK_CHUNK_LEN + 8 * 0) = 36 /\ slice bs NK_IF_NAME 960 = hw_ift_bytes.
Proof.
  intros bs H. unfold pr_check in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11] H12] H13] H14].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13. apply bl_eqb_eq in H14.
  repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma pr_nlk_wf : forall bs, pr_check bs = true -> nlk_wf bs.
Proof.
  intros bs Hb.
  destruct (pr_fields bs Hb) as (_ & Hc & Hn & Hs & Hi & Ho & Hod & Hcl & Hm & He1 & He2 & He3 & Hl0 & _).
  unfold nlk_wf, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  all: intros j Hj; assert (j = 0) by lia; subst j; lia.
Qed.

Definition z_check (mbs : list byte) : bool :=
  (Z.of_nat (length mbs) =? MD_SIZE) && (md_n_req mbs =? 0) && (md_next mbs =? 0) &&
  (md_socket_errno mbs =? 0) && (md_send_errno mbs =? 0) && (md_n_mark mbs =? 0).

Lemma pr_md_ok : z_check pr_md = true.
Proof. vm_compute. reflexivity. Qed.

Lemma z_fields : forall mbs, z_check mbs = true ->
  Z.of_nat (length mbs) = MD_SIZE /\ md_n_req mbs = 0 /\ md_next mbs = 0 /\ md_socket_errno mbs = 0 /\
  md_send_errno mbs = 0 /\ md_n_mark mbs = 0.
Proof.
  intros mbs H. unfold z_check in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[H1 H2] H3] H4] H5] H6]. apply Z.eqb_eq in H1, H2, H3, H4, H5, H6.
  repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma z_wf_of : forall mbs, z_check mbs = true -> model_wf mbs.
Proof.
  intros mbs Hm. destruct (z_fields mbs Hm) as (_ & Hn & Hx & Hs & Hd & Hk).
  unfold model_wf, model_marks_wf, slots_terminated, NL_SENT_MAX, NL_SENT_LEN, MARKS_MAX.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  all: intros i Hi; lia.
Qed.

Definition R_MZ : rg := RL HW_MB MD_SIZE pr_md.

(* ==========================================================================
   16. model_read (run R0, LLVMFuzzerTestOneInput 0x8368c) on "nl0" with wk, wa of 16
   ========================================================================== *)

Definition pr_rest : list rg := [R_NLS; R_NLR; R_GN; R_GNS; R_ODD; R_ODDS; R_WK; R_WA; R_FS; R_MZ; R_MBS; R_MBR].
Definition pr_rgs (bs : list byte) : list rg := RL LA_G_NL NK_SIZE bs :: pr_rest.
Definition PR_M : word -> option byte := rmem (pr_rgs pr_bs).
Definition PR0 : word -> option byte := rmem (pr_rgs []).

Lemma pr_disj : forall bs, rgs_disj (pr_rgs bs) = true.
Proof. intros bs. vm_compute. reflexivity. Qed.
Lemma pr_ext : forall bs, mext PR0 (rmem (pr_rgs bs)).
Proof. intros bs. exact (gl_ext bs pr_rest). Qed.
Lemma in_pr_NLS : forall bs, In R_NLS (pr_rgs bs).
Proof. intros bs. right. apply (nth_error_In pr_rest 0). reflexivity. Qed.
Lemma in_pr_MZ : forall bs, In R_MZ (pr_rgs bs).
Proof. intros bs. right. apply (nth_error_In pr_rest 9). reflexivity. Qed.
Lemma in_pr_MBS : forall bs, In R_MBS (pr_rgs bs).
Proof. intros bs. right. apply (nth_error_In pr_rest 10). reflexivity. Qed.

Lemma pr_ent_ok : forallb (entk_chk PR0 HW_SP MODEL_READ_AK) hw_ift = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pr_ok :
  bytes_chk PR0 HW_WK (repeat (zb 0) 16) = true /\ bytes_chk PR0 HW_WA (repeat (zb 0) 16) = true /\
  ra_chk PR0 HW_WK 16 = true /\ hull_chk PR0 HW_WK 16 = true /\
  ra_chk PR0 HW_WA 16 = true /\ hull_chk PR0 HW_WA 16 = true /\
  hull_chk PR0 HW_MB MD_SIZE = true /\ hull_chk PR0 (LA_G_NL + NK_CHUNK) NK_N_CHUNKS = true /\
  tab_apartb HW_WK 16 = true /\ tab_apartb HW_WA 16 = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

Lemma model_read_of : forall segs B regs bs (HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd),
  pr_check bs = true ->
  aarg regs 0 = HW_MB -> aarg regs 1 = LA_G_NAMES -> aarg regs 2 = HW_WK -> aarg regs 3 = 16 ->
  aarg regs 4 = HW_WA -> aarg regs 5 = 16 -> spZ regs = HW_SP ->
  model_read_apre segs B regs (rmem (pr_rgs bs)).
Proof.
  intros segs B regs bs HERR Hb H0 H1 H2 H3 H4 H5 Hsp.
  destruct (pr_fields bs Hb) as (Hlen & _ & _ & _ & Hnif & _ & _ & _ & _ & _ & _ & _ & _ & Hift).
  destruct (z_fields pr_md pr_md_ok) as (Hml & _).
  destruct pr_ok as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10).
  assert (E0 : nth_error hw_ift 0 = Some (LA_G_NAMES, nl_name 0, 2)) by reflexivity.
  destruct (gl_entry segs regs bs pr_rest HW_SP MODEL_READ_AK 0 LA_G_NAMES (nl_name 0) 2 Hlen Hift Hsp
              pr_ent_ok E0) as (_ & _ & _ & _ & _ & _ & Hc & Ha).
  unfold model_read_apre. rewrite H0, H1, H2, H3, H4, H5.
  exists pr_md, bs, hw_tab, (Some (nl_name 0)).
  split.
  { split; [|exact Hml].
    apply (rl_au8arr segs (pr_rgs bs) _ HW_MB MD_SIZE);
      [apply mext_refl | apply pr_disj | apply in_pr_MZ | exact Hml | zle | zle]. }
  split; [exact (z_wf_of pr_md pr_md_ok)|].
  split; [exact (gl_anlk segs bs pr_rest Hlen)|].
  split; [exact (pr_nlk_wf bs Hb)|].
  split; [exact (gl_iftab segs regs bs pr_rest HW_SP MODEL_READ_AK Hlen Hnif Hift Hsp pr_ent_ok)|].
  split; [split; [unfold LA_G_NAMES; discriminate | exact Hc]|].
  split.
  { intros _ _. exists (repeat (zb 0) 16). split; [reflexivity|].
    apply (au8arr_chk segs PR0 _ HW_WK _ (pr_ext bs) W1); zle. }
  split.
  { intros _ _. exists (repeat (zb 0) 16). split; [reflexivity|].
    apply (au8arr_chk segs PR0 _ HW_WA _ (pr_ext bs) W2); zle. }
  rewrite hw_tab_len.
  split.
  { apply (ra_fill segs (pr_rgs bs) _ S_NL 33999); [apply mext_refl | apply pr_disj | apply in_pr_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_NAME) (8 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split.
  { apply (ra_fill segs (pr_rgs bs) _ S_NL 33999); [apply mext_refl | apply pr_disj | apply in_pr_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_INDEX) (4 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split; [intros s Hs; injection Hs as <-; exact Ha|].
  split; [exact (gl_tabstr segs regs bs pr_rest HW_SP MODEL_READ_AK Hlen Hift Hsp pr_ent_ok)|].
  split.
  { apply (ra_fill segs (pr_rgs bs) _ S_MB 1107); [apply mext_refl | apply pr_disj | apply in_pr_MBS | zle | zle |].
    intros x Hx. apply (shadow_win HW_MB MD_SIZE); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs PR0 _ _ _ (pr_ext bs) W7)|].
  split; [unfold amem_range; right; split; zle|].
  split.
  { apply (ra_fill segs (pr_rgs bs) _ S_NL 33999); [apply mext_refl | apply pr_disj | apply in_pr_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs PR0 _ _ _ (pr_ext bs) W8)|].
  split; [unfold apart_gnl; right; zle|].
  split; [unfold apart_frame; rewrite Hsp; left; zle|].
  split; [intros _; unfold apart_frame; rewrite Hsp; left; zle|].
  split; [intros _; unfold apart_frame; rewrite Hsp; left; zle|].
  (* errno: every object is above kLowMemEnd, errno below it (HERR) *)
  split; [unfold apart; left; apply (Z.le_trans _ kLowMemEnd); [exact (proj2 HERR) | zle]|].
  split; [intros _ _; unfold apart; left; apply (Z.le_trans _ kLowMemEnd); [exact (proj2 HERR) | zle]|].
  split; [intros _ _; unfold apart; left; apply (Z.le_trans _ kLowMemEnd); [exact (proj2 HERR) | zle]|].
  split.
  { intros _ _. split; [unfold apart_gnl; right; zle|]. split; [unfold apart; right; zle|].
    split; [exact (gl_tab_apart segs regs bs pr_rest HW_SP MODEL_READ_AK HW_WK 16 Hlen Hift Hsp pr_ent_ok W9
                     ltac:(zle) ltac:(zle))|].
    split; [unfold amem_range; right; split; zle|].
    split; [exact (ra_chk_ok segs PR0 _ _ _ (pr_ext bs) W3) | exact (hull_chk_ok segs PR0 _ _ _ (pr_ext bs) W4)]. }
  split.
  { intros _ _. split; [unfold apart_gnl; right; zle|]. split; [unfold apart; right; zle|].
    split; [exact (gl_tab_apart segs regs bs pr_rest HW_SP MODEL_READ_AK HW_WA 16 Hlen Hift Hsp pr_ent_ok W10
                     ltac:(zle) ltac:(zle))|].
    split; [unfold amem_range; right; split; zle|].
    split; [exact (ra_chk_ok segs PR0 _ _ _ (pr_ext bs) W5) | exact (hull_chk_ok segs PR0 _ _ _ (pr_ext bs) W6)]. }
  split.
  { intros s Hs. injection Hs as <-. split; intros _ _; unfold apart; right; zle. }
  intros _ _ _ _. unfold apart. left. zle.
Qed.

(* the Pre lambda of model_read_acontract holds at PR_M, for every segment list and every asyms B whose errno lies
   below kLowMemEnd (HERR), at every register file with a0 = HW_MB (the model block), a1 = &g_names[0] ("nl0"),
   a2 = wk, a3 = 16, a4 = wa, a5 = 16 and sp = HW_SP *)
Lemma model_read_apre_sat : forall segs B (regs : bvmap 5 word)
  (HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd),
  aarg regs 0 = HW_MB -> aarg regs 1 = LA_G_NAMES -> aarg regs 2 = HW_WK -> aarg regs 3 = 16 ->
  aarg regs 4 = HW_WA -> aarg regs 5 = 16 -> spZ regs = HW_SP -> model_read_apre segs B regs PR_M.
Proof.
  intros segs B regs HERR H0 H1 H2 H3 H4 H5 Hsp.
  exact (model_read_of segs B regs pr_bs HERR pr_check_ok H0 H1 H2 H3 H4 H5 Hsp).
Qed.

(* ==========================================================================
   17. model_write (run W, LLVMFuzzerTestOneInput 0x83858) of "reac-pw:served" on "nl0"
   ========================================================================== *)

(* texts[1] in .rodata, and its shadow byte address *)
Definition A_SERVED : Z := 0x21100.
Definition S_TX : Z := 0x7fffc220.
Lemma S_TX_eq : S_TX = shadow_addr A_SERVED.
Proof. reflexivity. Qed.
Definition s_minted : list byte := map zb [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100].
(* .rodata [0x21100, 0x21140): the slots of texts[1] and texts[2] *)
Definition tx_bytes : list byte := pad 32 S_SERVED ++ pad 32 s_minted.
Definition tx_sh : list byte := map zb [0; 7; 0xf9; 0xf9; 0; 7; 0xf9; 0xf9].
Definition R_TX : rg := RL A_SERVED 64 tx_bytes.
Definition R_TXS : rg := RL S_TX 8 tx_sh.

Definition pw_rest : list rg := [R_NLS; R_NLR; R_GN; R_GNS; R_ODD; R_ODDS; R_TX; R_TXS; R_MZ; R_MBS; R_MBR].
Definition pw_rgs (bs : list byte) : list rg := RL LA_G_NL NK_SIZE bs :: pw_rest.
Definition PW_M : word -> option byte := rmem (pw_rgs pr_bs).
Definition PW0 : word -> option byte := rmem (pw_rgs []).

Lemma pw_disj : forall bs, rgs_disj (pw_rgs bs) = true.
Proof. intros bs. vm_compute. reflexivity. Qed.
Lemma pw_ext : forall bs, mext PW0 (rmem (pw_rgs bs)).
Proof. intros bs. exact (gl_ext bs pw_rest). Qed.
Lemma in_pw_NLS : forall bs, In R_NLS (pw_rgs bs).
Proof. intros bs. right. apply (nth_error_In pw_rest 0). reflexivity. Qed.
Lemma in_pw_MZ : forall bs, In R_MZ (pw_rgs bs).
Proof. intros bs. right. apply (nth_error_In pw_rest 8). reflexivity. Qed.
Lemma in_pw_MBS : forall bs, In R_MBS (pw_rgs bs).
Proof. intros bs. right. apply (nth_error_In pw_rest 9). reflexivity. Qed.

Lemma pw_ent_ok : forallb (entk_chk PW0 HW_SP MODEL_WRITE_AK) hw_ift = true.
Proof. vm_compute. reflexivity. Qed.

Lemma pw_ok :
  cstr_chk PW0 A_SERVED S_SERVED = true /\ sarg_chk PW0 HW_SP MODEL_WRITE_AK A_SERVED S_SERVED = true /\
  bytes_chk PW0 (A_SERVED + Z.of_nat (length S_SERVED) + 1) [zb 0] = true /\
  hull_chk PW0 HW_MB MD_SIZE = true /\ hull_chk PW0 (LA_G_NL + NK_CHUNK) NK_N_CHUNKS = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

Lemma model_write_of : forall segs B regs bs (HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd),
  pr_check bs = true ->
  aarg regs 0 = HW_MB -> aarg regs 1 = LA_G_NAMES -> aarg regs 2 = A_SERVED -> spZ regs = HW_SP ->
  model_write_apre segs B regs (rmem (pw_rgs bs)).
Proof.
  intros segs B regs bs HERR Hb H0 H1 H2 Hsp.
  destruct (pr_fields bs Hb) as (Hlen & _ & _ & _ & Hnif & _ & _ & _ & _ & _ & _ & _ & _ & Hift).
  destruct (z_fields pr_md pr_md_ok) as (Hml & _).
  destruct pw_ok as (V1 & V2 & V3 & V4 & V5).
  assert (E0 : nth_error hw_ift 0 = Some (LA_G_NAMES, nl_name 0, 2)) by reflexivity.
  destruct (gl_entry segs regs bs pw_rest HW_SP MODEL_WRITE_AK 0 LA_G_NAMES (nl_name 0) 2 Hlen Hift Hsp
              pw_ent_ok E0) as (_ & _ & _ & _ & _ & _ & Hc & Ha).
  pose proof (sarg_chk_ok segs regs PW0 _ HW_SP MODEL_WRITE_AK A_SERVED S_SERVED (pw_ext bs) Hsp V2) as As.
  unfold model_write_apre. rewrite H0, H1, H2.
  exists pr_md, bs, hw_tab, (Some (nl_name 0)), (Some S_SERVED).
  split.
  { split; [|exact Hml].
    apply (rl_au8arr segs (pw_rgs bs) _ HW_MB MD_SIZE);
      [apply mext_refl | apply pw_disj | apply in_pw_MZ | exact Hml | zle | zle]. }
  split; [exact (z_wf_of pr_md pr_md_ok)|].
  split; [exact (gl_anlk segs bs pw_rest Hlen)|].
  split; [exact (pr_nlk_wf bs Hb)|].
  split; [exact (gl_iftab segs regs bs pw_rest HW_SP MODEL_WRITE_AK Hlen Hnif Hift Hsp pw_ent_ok)|].
  split; [split; [unfold LA_G_NAMES; discriminate | exact Hc]|].
  split; [split; [unfold A_SERVED; discriminate | exact (acstr_chk segs PW0 _ A_SERVED S_SERVED (pw_ext bs) V1)]|].
  rewrite hw_tab_len.
  split.
  { apply (ra_fill segs (pw_rgs bs) _ S_NL 33999); [apply mext_refl | apply pw_disj | apply in_pw_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_NAME) (8 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split.
  { apply (ra_fill segs (pw_rgs bs) _ S_NL 33999); [apply mext_refl | apply pw_disj | apply in_pw_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_IF_INDEX) (4 * 64)); [reflexivity | zle | zle | exact Hx]. }
  split; [intros s Hs; injection Hs as <-; exact Ha|].
  split; [exact (gl_tabstr segs regs bs pw_rest HW_SP MODEL_WRITE_AK Hlen Hift Hsp pw_ent_ok)|].
  split.
  { intros s Hs. injection Hs as <-. destruct As as (_ & A1 & A2 & A3 & A4 & A5 & _).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    exists [zb 0]. split; [exact (abytes_chk segs PW0 _ _ [zb 0] (pw_ext bs) V3 ltac:(zle) ltac:(zle)) | zle]. }
  split.
  { apply (ra_fill segs (pw_rgs bs) _ S_MB 1107); [apply mext_refl | apply pw_disj | apply in_pw_MBS | zle | zle |].
    intros x Hx. apply (shadow_win HW_MB MD_SIZE); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs PW0 _ _ _ (pw_ext bs) V4)|].
  split; [unfold amem_range; right; split; zle|].
  split.
  { apply (ra_fill segs (pw_rgs bs) _ S_NL 33999); [apply mext_refl | apply pw_disj | apply in_pw_NLS | zle | zle |].
    intros x Hx. apply (shadow_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS); [reflexivity | zle | zle | exact Hx]. }
  split; [exact (hull_chk_ok segs PW0 _ _ _ (pw_ext bs) V5)|].
  split; [unfold apart_gnl; right; zle|].
  split; [unfold apart_frame; rewrite Hsp; left; zle|].
  (* errno: the model block is above kLowMemEnd, errno below it (HERR) *)
  unfold apart. left. apply (Z.le_trans _ kLowMemEnd); [exact (proj2 HERR) | zle].
Qed.

(* the Pre lambda of model_write_acontract holds at PW_M, for every segment list and every asyms B whose errno lies
   below kLowMemEnd (HERR), at every register file with a0 = HW_MB (the model block), a1 = &g_names[0] ("nl0"),
   a2 = texts[1] ("reac-pw:served") and sp = HW_SP *)
Lemma model_write_apre_sat : forall segs B (regs : bvmap 5 word)
  (HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd),
  aarg regs 0 = HW_MB -> aarg regs 1 = LA_G_NAMES -> aarg regs 2 = A_SERVED -> spZ regs = HW_SP ->
  model_write_apre segs B regs PW_M.
Proof.
  intros segs B regs HERR H0 H1 H2 Hsp. exact (model_write_of segs B regs pr_bs HERR pr_check_ok H0 H1 H2 Hsp).
Qed.

(* ==========================================================================
   18. The assumptions of the thirteen lemmas
   ========================================================================== *)

Print Assumptions check_refused_apre_sat.
Print Assumptions check_verdict_apre_sat.
Print Assumptions check_write_apre_sat.
Print Assumptions check_mark_apre_sat.
Print Assumptions text_buf_apre_sat.
Print Assumptions check_socket_apre_sat.
Print Assumptions index_of_apre_sat.
Print Assumptions check_bounds_apre_sat.
Print Assumptions check_read_apre_sat.
Print Assumptions check_requests_apre_sat.
Print Assumptions check_marks_apre_sat.
Print Assumptions model_read_apre_sat.
Print Assumptions model_write_apre_sat.

(* ==========================================================================
   PART B: talk and text_of (every name defined below starts with hb_ / HB_)
   ==========================================================================
   Satisfiability witnesses of the function-specific Pre of two image-A contracts (talk_c.v, text_of_c.v), at
   memories holding the values a real run holds at the call (each header's SATISFIABILITY WITNESS paragraph). As in
   form_witness.v, the journal part of the Pre (link_amem.v `apre`) needs AR of image A's start state and is not here.
   - hb_talk_apre_sat: talk, called by model_read at +0x1e8 (0x86614). The run: the first op is op_read of "nl0"
     (name byte 0, index_of "nl0" = 2) with kc = ac = 16; kernel(): flags 0, errno byte 0, end-errno byte 0, one raw
     chunk of 40 bytes (nlmsghdr length 40, type 16, seq 1; ifinfomsg 0; IFLA_IFALIAS rta_len 7, "ab", NUL, one pad
     byte). Registers: a0 = M = 0x621000000100 (the calloc(1, 8856) model block, all 0 after model_begin), a1 = R =
     0x7f0000008020 (model_read's class-1 side frame 0x7f0000008000 + 0x20) holding req_read 2, a2 = 32, a3 = WK =
     0x7f00001002e0 and a5 = WA = 0x7f0000100330 (LLVMFuzzerTestOneInput's class-4 side frame 0x7f0000100000, +0x2e0
     and +0x330: wk[40], wa[40], 40 zero bytes each), a4 = a6 = 16, sp = 0x7fffffffede0 (model_read's realigned sp).
     g_nl (`hb_kbs`): interfaces()'s table (60 entries g_names + 8 k with index k + 2, k < 64, k mod 16 <> 15; then
     odd[1..4] = 0x20fe0, 0x21000, 0x21020, 0x21040 with index 101..104, read from the pin's .data.rel.ro at LA_ODD;
     n_if = 64), kernel()'s chunk queue (n_chunks 1, chunk_len[0] = 40, chunk[0] the 40 bytes), next 0, end_errno 105
     (nl_errno(0) = ENOBUFS), every other count and errno 0. Its fields and nlk_wf come from ONE vm_compute
     (`hb_kchk_ok`); the proof is over an abstract list with those fields as hypotheses. The shadow bytes over each
     range the Pre names and over its hull are 0 (M is whole granules; frame_alloc_1 zeroes R's frame;
     LLVMFuzzerTestOneInput zeroes the shadow of wk / wa; g_nl is an image object).
   - hb_text_of_apre_sat: text_of, called by LLVMFuzzerTestOneInput at 0x82e24 (op_decide's first text_of), input
     04 05 00 (N = 3, selector 0x05: bit 7 clear) in the input block d = 0x602000000010. Registers: sp = s1 =
     0x7ffffffeee60, a0 = p = s1 + 0x118 (the cursor: c0 = d + 1, c1 = 2), a1 = o = s1 + 0x130 (the slot own
     points to: 0, stack residue). [o - 8] = 0 (residue) and [o - 16] = [p + 8] = 2 <= o. The shadow byte of the
     input's granule is 3 (malloc(3)); the shadow bytes over p, o, the texts table and the hulls are 0. The table at
     LA_TEXTS = 0xa17c0 holds the 11 pointers of the header, and each string is in the witness memory (pointers and
     strings read again from the pin, sha256 059dae63e07c, with pyelftools on 2026-10-30: they agree with
     text_of_c.v's header). Three facts of the instance and not of memory are HYPOTHESES:
     `hb_tx_ro segs rlo rhi B`: each of the 11 strings s at q, to q + |s| + 1 (the string and its NUL), is
       `text_of_ro` (in_roP of segs / rlo / rhi, outside B's runtime statics and errno). No memory makes it true for
       every segs (segs = [] with rlo = rhi makes in_roP false). The instance discharges it from the read-only PT_LOAD
       [0x10000, 0x3026c), which holds .rodata [0x102e0, 0x22fac) and so the eleven strings with their NULs, outside
       the literals' redzones (which are in as_owned_static).
     `text_of_traces B`: it waits for the start-up universe (ACejUniv.v Tfib_univ_wild).
     HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd: the errno conjunct `apart (as_errno B) 4 p 16`
       follows from it, p being above kLowMemEnd (the malloc rule's kept clause, `ascratch`, excepts errno, so the
       Pre separates the cursor from it). No memory places the abstract as_errno B. It is the first conjunct of
       `api_env`; the instance discharges it by TfibLib's `tl_errno` (PART A's ERRNO paragraph:
       as_errno B = TFIB_ERRNO = 0x631b6c).
   Each lemma holds for every segment list: the witness memory holds every byte the Pre reads, so no ROM byte is read.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem form_witness talk_c text_of_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Decidable checks over a memory function, and their soundness. Every fact over big constants is proved by a
      closed boolean computation; `lia` sees only abstract numbers (division by 8 with the image's 2^43-sized
      constants makes `lia` slow).
   ========================================================================== *)

Ltac hb_zle := apply Z.leb_le; vm_compute; reflexivity.
Ltac hb_zlt := apply Z.ltb_lt; vm_compute; reflexivity.

Lemma hb_le_or : forall a b c d, ((a <=? b) || (c <=? d)) = true -> a <= b \/ c <= d.
Proof. intros a b c d H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; [left|right]; exact H. Qed.
Ltac hb_or := apply hb_le_or; vm_compute; reflexivity.

(* two option bytes, compared by value *)
Definition hb_oeq (x y : option byte) : bool :=
  match x, y with Some a, Some b => bv_unsigned a =? bv_unsigned b | _, _ => false end.
Lemma hb_oeq_ok : forall x y, hb_oeq x y = true -> x = y.
Proof.
  intros [a|] [b|] H; cbn in H; try discriminate H.
  apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H.
Qed.

(* the bytes bs at a *)
Definition hb_chk (m : word -> option byte) (a : Z) (bs : list byte) : bool :=
  forallb (fun i => hb_oeq (m (Z_to_bv 64 (a + Z.of_nat i))) (nth_error bs i)) (seq 0 (length bs)).

Lemma hb_chk_at : forall m a bs, hb_chk m a bs = true ->
  forall i, (i < length bs)%nat -> m (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i.
Proof.
  intros m a bs H i Hi. unfold hb_chk in H. rewrite forallb_forall in H.
  apply hb_oeq_ok. apply H. apply in_seq. lia.
Qed.

Lemma hb_chk_lift : forall (m1 m2 : word -> option byte) a bs,
  (forall w b, m1 w = Some b -> m2 w = Some b) -> hb_chk m1 a bs = true -> hb_chk m2 a bs = true.
Proof.
  unfold hb_chk. intros m1 m2 a bs Hl H. rewrite forallb_forall in *. intros i Hi. specialize (H i Hi).
  destruct (m1 (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:E; [|cbn in H; discriminate H].
  rewrite (Hl _ _ E). exact H.
Qed.

Lemma hb_au8arr_fn : forall segs (m : word -> option byte) a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> m (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i) -> au8arr segs m a bs.
Proof.
  intros segs m a bs Ha Hb Hat. split.
  - split; [exact Ha|]. split; [exact Hb|]. intros i Hi. unfold mbyte. rewrite (Hat i Hi).
    destruct (nth_error bs i) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
  - intros i Hi. unfold writable_at, wview. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (Hat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) eqn:E; [cbv beta iota; discriminate|]. apply nth_error_None in E. lia.
Qed.

Lemma hb_au8arr : forall segs m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> hb_chk m a bs = true ->
  au8arr segs m a bs.
Proof. intros segs m a bs Ha Hb Hc. exact (hb_au8arr_fn segs m a bs Ha Hb (hb_chk_at m a bs Hc)). Qed.

Lemma hb_chk_some : forall segs m a bs i, hb_chk m a bs = true -> 0 <= i < Z.of_nat (length bs) ->
  ard segs m (a + i) <> None.
Proof.
  intros segs m a bs i Hc Hi. pose proof (hb_chk_at m a bs Hc (Z.to_nat i) ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. unfold ard, mbyte. rewrite E.
  destruct (nth_error bs (Z.to_nat i)) eqn:N; [cbv [option_map]; discriminate|]. apply nth_error_None in N. lia.
Qed.

(* the n little-endian bytes of v at a *)
Definition hb_vchk (m : word -> option byte) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => hb_oeq (m (Z_to_bv 64 (a + Z.of_nat k))) (Some (Z_to_bv 8 (YO0f.le_byte v n k)))) (seq 0 n).

Lemma hb_val_mem : forall segs m a n v, hb_vchk m a n v = true -> val_mem segs m a n v.
Proof.
  intros segs m a n v H. unfold val_mem. intros k Hk. unfold hb_vchk in H. rewrite forallb_forall in H.
  unfold mbyte. rewrite (hb_oeq_ok _ _ (H k ltac:(apply in_seq; lia))). reflexivity.
Qed.

(* eight bytes fix a value in [0, 2^64) (Reusable/YG0s.v le_bytes8, over YO0f.le_byte) *)
Lemma hb_le_byte_8 : forall v k, YO0f.le_byte v 8 k = (v mod 2 ^ 64) / 2 ^ (8 * Z.of_nat k) mod 256.
Proof. intros v k. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma hb_le_bytes8 : forall v, 0 <= v < 2 ^ 64 ->
  YO0f.le_byte v 8 0 + 256 * (YO0f.le_byte v 8 1 + 256 * (YO0f.le_byte v 8 2 + 256 * (YO0f.le_byte v 8 3
  + 256 * (YO0f.le_byte v 8 4 + 256 * (YO0f.le_byte v 8 5 + 256 * (YO0f.le_byte v 8 6
  + 256 * YO0f.le_byte v 8 7)))))) = v.
Proof.
  intros v Hv. rewrite !hb_le_byte_8. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity. rewrite Z.div_1_r.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 2)) with (256 * 256) by reflexivity.
  replace (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256) by reflexivity.
  replace (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
  rewrite <- !Z.div_div by lia.
  set (v1 := v / 256). set (v2 := v1 / 256). set (v3 := v2 / 256). set (v4 := v3 / 256). set (v5 := v4 / 256).
  set (v6 := v5 / 256). set (v7 := v6 / 256).
  assert (E7 : v7 mod 256 = v7).
  { apply Z.mod_small. subst v7 v6 v5 v4 v3 v2 v1.
    split; [repeat (apply Z.div_pos; [|lia]); lia|].
    repeat (apply Z.div_lt_upper_bound; [lia|]).
    change (2 ^ 64) with (256 * (256 * (256 * (256 * (256 * (256 * (256 * 256))))))) in Hv. lia. }
  rewrite E7.
  assert (R : forall x, x mod 256 = x - 256 * (x / 256)) by (intros x; pose proof (Z.div_mod x 256 ltac:(lia)); lia).
  rewrite (R v), (R v1), (R v2), (R v3), (R v4), (R v5), (R v6). subst v7 v6 v5 v4 v3 v2 v1. lia.
Qed.

Lemma hb_zb_inj : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z_to_bv 8 x = Z_to_bv 8 y -> x = y.
Proof.
  intros x y Hx Hy H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  unfold bv_wrap in H. change (bv_modulus 8) with 256 in H. rewrite !Z.mod_small in H by lia. exact H.
Qed.

Lemma hb_u64_unique : forall segs m a v w, val_mem segs m a 8 v -> val_mem segs m a 8 w ->
  0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> w = v.
Proof.
  intros segs m a v w Hv Hw Rv Rw.
  assert (E : forall k, (k < 8)%nat -> YO0f.le_byte w 8 k = YO0f.le_byte v 8 k).
  { intros k Hk. apply hb_zb_inj; [unfold YO0f.le_byte; apply Z.mod_pos_bound; lia
                                  | unfold YO0f.le_byte; apply Z.mod_pos_bound; lia |].
    pose proof (Hv k Hk) as A. pose proof (Hw k Hk) as C. rewrite A in C. congruence. }
  rewrite <- (hb_le_bytes8 w Rw), <- (hb_le_bytes8 v Rv).
  rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia.
  reflexivity.
Qed.

(* shadow windows: the window of an object [a, a + n) covers its shadow bytes and their hull *)
Definition hb_win (a n : Z) : Z * Z := (SHADOW_OFF + a / 8 - 8, n / 8 + 24).
Definition hb_sh (ws : list (Z * Z)) (s : Z) : bool := existsb (fun r => inrz s (fst r) (snd r)) ws.

Lemma hb_sh_in : forall ws r s, In r ws -> fst r <= s < fst r + snd r -> hb_sh ws s = true.
Proof.
  intros ws r s Hr Hs. unfold hb_sh. apply existsb_exists. exists r. split; [exact Hr | apply inrz_true; exact Hs].
Qed.

Definition hb_disj (ws : list (Z * Z)) (lo n : Z) : bool :=
  forallb (fun r => (lo + n <=? fst r) || (fst r + snd r <=? lo)) ws.

Lemma hb_sh_out : forall ws lo n s, hb_disj ws lo n = true -> lo <= s < lo + n -> hb_sh ws s = false.
Proof.
  intros ws lo n s Hd Hs. unfold hb_sh. apply not_true_is_false. intros E.
  apply existsb_exists in E as (r & Hr & Hi). unfold hb_disj in Hd. rewrite forallb_forall in Hd.
  specialize (Hd r Hr). unfold inrz in Hi. apply andb_prop in Hi as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.

Definition hb_wins_ok (ws : list (Z * Z)) : bool :=
  forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 64)) ws.

Lemma hb_win_rng : forall ws r s, hb_wins_ok ws = true -> In r ws -> fst r <= s < fst r + snd r -> 0 <= s < 2 ^ 64.
Proof.
  intros ws r s Hw Hr Hs. unfold hb_wins_ok in Hw. rewrite forallb_forall in Hw. specialize (Hw r Hr).
  apply andb_prop in Hw as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

(* a in [lo', lo' + n') is outside [lo, lo + n) when the two ranges are apart *)
Lemma hb_inrz_out : forall a lo n lo' n', ((lo' + n' <=? lo) || (lo + n <=? lo')) = true -> lo' <= a < lo' + n' ->
  inrz a lo n = false.
Proof. intros a lo n lo' n' H Ha. apply inrz_false. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia. Qed.

Lemma hb_inrz_ne : forall g lo n s, inrz g lo n = false -> lo <= s < lo + n -> s <> g.
Proof. intros g lo n s H Hs E. subst g. rewrite inrz_true in H by exact Hs. discriminate H. Qed.

(* the shadow bytes of [a, a + n) lie in [lo, lo + len), where m holds 0 *)
Lemma hb_ra_of : forall segs (m : word -> option byte) a n lo len,
  lo + 8 <= SHADOW_OFF + a / 8 -> SHADOW_OFF + (a + n) / 8 + 8 <= lo + len ->
  (forall s, lo <= s < lo + len -> m (Z_to_bv 64 s) = Some (zb 0)) ->
  range_addressable (ard segs m) SHADOW_OFF a n.
Proof.
  intros segs m a n lo len H1 H2 H x Hx. exists 0. split; [|left; reflexivity].
  assert (a / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (x / 8 <= (a + n) / 8) by (apply Z.div_le_mono; lia).
  unfold ard, mbyte, shadow_of_addr. rewrite H by lia. reflexivity.
Qed.

(* the hull of [a, a + n) lies in [lo, lo + len), where every byte of m is present *)
Lemma hb_hull_of : forall segs (m : word -> option byte) a n lo len, 0 <= n ->
  lo + 8 <= SHADOW_OFF + a / 8 -> SHADOW_OFF + (a + n) / 8 + 8 <= lo + len ->
  (forall s, lo <= s < lo + len -> m (Z_to_bv 64 s) <> None) ->
  shadow_hull_vis (ard segs m) a n.
Proof.
  intros segs m a n lo len Hn H1 H2 H s Hs. unfold shadow_addr in Hs.
  assert ((a + n - 1) / 8 <= (a + n) / 8) by (apply Z.div_le_mono; lia).
  assert (L : (SHADOW_OFF + a / 8) / 8 * 8 > SHADOW_OFF + a / 8 - 8).
  { pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)). lia. }
  assert (U : (SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8).
  { pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)). lia. }
  unfold ard, mbyte. destruct (m (Z_to_bv 64 s)) as [b|] eqn:E; [cbv [option_map]; discriminate|].
  exfalso. apply (H s); [lia | exact E].
Qed.

Lemma hb_zb_val : forall v, 0 <= v < 256 -> bv_unsigned (zb v) = v.
Proof.
  intros v Hv. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hv.
Qed.

(* [x0, x0 + n) inside the first v bytes of the granule at g, whose shadow byte is v (a partial granule) *)
Lemma hb_ra_part : forall segs (m : word -> option byte) g v x0 n, g mod 8 = 0 -> 0 < v < 8 -> g <= x0 ->
  x0 + n <= g + v -> m (Z_to_bv 64 (SHADOW_OFF + g / 8)) = Some (zb v) ->
  range_addressable (ard segs m) SHADOW_OFF x0 n.
Proof.
  intros segs m g v x0 n Hg Hv H1 H2 H x Hx.
  pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  assert (E : x / 8 = g / 8) by lia.
  exists v. split.
  - unfold ard, mbyte, shadow_of_addr. rewrite E, H. cbv [option_map]. f_equal. apply hb_zb_val. lia.
  - right. split; lia.
Qed.

(* ==========================================================================
   2. talk, called by model_read at +0x1e8 (0x86614), op_read of "nl0" with kc = ac = 16
   ========================================================================== *)

(* the model block (calloc(1, 8856)), the request in model_read's class-1 side frame, wk / wa in
   LLVMFuzzerTestOneInput's class-4 side frame, model_read's realigned sp *)
Definition HB_TK_M : Z := 0x621000000100.
Definition HB_TK_R : Z := 0x7f0000008020.
Definition HB_TK_WK : Z := 0x7f00001002e0.
Definition HB_TK_WA : Z := 0x7f0000100330.
Definition HB_TK_SP : Z := 0x7fffffffede0.

(* the RTM_GETLINK model_read builds for index 2 *)
Definition hb_tk_req : list byte := req_read 2.

Definition hb_tk_shw : list (Z * Z) :=
  [hb_win HB_TK_M MD_SIZE; hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS; hb_win HB_TK_R 32;
   hb_win HB_TK_WK 40; hb_win HB_TK_WA 40].

(* every byte but g_nl's *)
Definition hb_tk_small (w : word) : option byte :=
  if hb_sh hb_tk_shw (bv_unsigned w) then Some (zb 0)
  else if inrz (bv_unsigned w) HB_TK_M MD_SIZE then Some (zb 0)
  else if inrz (bv_unsigned w) HB_TK_R 32 then nth_error hb_tk_req (Z.to_nat (bv_unsigned w - HB_TK_R))
  else if inrz (bv_unsigned w) HB_TK_WK 40 then Some (zb 0)
  else if inrz (bv_unsigned w) HB_TK_WA 40 then Some (zb 0)
  else None.

(* and g_nl's bytes kbs at LA_G_NL *)
Definition hb_tk_mem (kbs : list byte) (w : word) : option byte :=
  match hb_tk_small w with Some b => Some b | None => g_mem kbs w end.

(* g_nl after interfaces() and kernel() *)
Definition hb_chunk0 : list byte :=
  map zb [40; 0; 0; 0; 16; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0] ++ repeat (zb 0) 16 ++
  map zb [7; 0; 20; 0; 0x61; 0x62; 0; 0].
Definition hb_if_ks : list Z := filter (fun k => negb (k mod 16 =? 15)) (map Z.of_nat (seq 0 64)).
Definition hb_if_names : list Z :=
  map (fun k => LA_G_NAMES + 8 * k) hb_if_ks ++ [0x20fe0; 0x21000; 0x21020; 0x21040].
Definition hb_if_idx : list Z := map (fun k => k + 2) hb_if_ks ++ [101; 102; 103; 104].
Definition hb_if_tab : list byte :=
  flat_map (wle_bytes 8) hb_if_names ++ repeat (zb 0) 128 ++ flat_map (wle_bytes 4) hb_if_idx ++ repeat (zb 0) 64.
Definition hb_kbs : list byte :=
  hb_chunk0 ++ repeat (zb 0) (Z.to_nat (NK_CHUNK_LEN - 40)) ++                     (* chunk *)
  wle_bytes 8 40 ++ repeat (zb 0) (Z.to_nat (NK_N_CHUNKS - NK_CHUNK_LEN - 8)) ++     (* chunk_len *)
  wle_bytes 4 1 ++ wle_bytes 4 0 ++ wle_bytes 4 105 ++                              (* n_chunks, next, end_errno *)
  repeat (zb 0) (Z.to_nat (NK_IF_NAME - NK_SOCKET_ERRNO)) ++                        (* errnos .. n_sent *)
  hb_if_tab ++ wle_bytes 4 64 ++ repeat (zb 0) 4.                                   (* if_name, if_index, n_if *)

(* The fields, checked by ONE computation over the 271992-byte list; the proofs below are over an abstract list. *)
Definition hb_kchk (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? NK_SIZE) &&
  (nk_n_chunks bs =? 1) && (nk_next bs =? 0) && (nk_n_sent bs =? 0) && (nk_n_if bs =? 64) &&
  (nk_open bs =? 0) && (nk_opened bs =? 0) && (nk_closed bs =? 0) && (nk_misuse bs =? 0) &&
  (nk_end_errno bs =? 105) && (nk_socket_errno bs =? 0) && (nk_send_errno bs =? 0) &&
  (fld_u64 bs (NK_CHUNK_LEN + 8 * 0) =? 40) &&
  bl_eqb (nk_chunk bs 0) hb_chunk0 && bl_eqb (slice bs NK_IF_NAME (NK_N_IF - NK_IF_NAME)) hb_if_tab.
Lemma hb_kchk_ok : hb_kchk hb_kbs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hb_kfields : forall bs, hb_kchk bs = true ->
  Z.of_nat (length bs) = NK_SIZE /\ nk_n_chunks bs = 1 /\ nk_next bs = 0 /\ nk_n_sent bs = 0 /\
  nk_n_if bs = 64 /\ nk_open bs = 0 /\ nk_opened bs = 0 /\ nk_closed bs = 0 /\ nk_misuse bs = 0 /\
  nk_end_errno bs = 105 /\ nk_socket_errno bs = 0 /\ nk_send_errno bs = 0 /\
  fld_u64 bs (NK_CHUNK_LEN + 8 * 0) = 40.
Proof.
  intros bs H. unfold hb_kchk in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  repeat rewrite andb_true_iff in H.
  repeat match type of H with
  | _ /\ _ => let H1 := fresh "H" in destruct H as [H H1]; apply Z.eqb_eq in H1
  end.
  apply Z.eqb_eq in H. repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma hb_kwf : forall bs, hb_kchk bs = true -> nlk_wf bs.
Proof.
  intros bs Hb.
  destruct (hb_kfields bs Hb) as (_ & Hc & Hn & Hs & Hi & Ho & Hod & Hcl & Hm & He1 & He2 & He3 & Hl0).
  unfold nlk_wf, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  all: intros j Hj; first [lia | (assert (j = 0) by lia); subst j; lia].
Qed.

(* the model block after model_begin: 8856 zero bytes *)
Definition hb_tk_mbs : list byte := repeat (zb 0) (Z.to_nat MD_SIZE).
Definition hb_mchk (mbs : list byte) : bool :=
  (Z.of_nat (length mbs) =? MD_SIZE) && (md_n_req mbs =? 0) && (md_next mbs =? 0) &&
  (md_socket_errno mbs =? 0) && (md_send_errno mbs =? 0) && (md_n_mark mbs =? 0) &&
  hb_chk hb_tk_small HB_TK_M mbs.
Lemma hb_mchk_ok : hb_mchk hb_tk_mbs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma hb_mfields : forall mbs, hb_mchk mbs = true ->
  Z.of_nat (length mbs) = MD_SIZE /\ md_n_req mbs = 0 /\ md_next mbs = 0 /\ md_socket_errno mbs = 0 /\
  md_send_errno mbs = 0 /\ md_n_mark mbs = 0 /\ hb_chk hb_tk_small HB_TK_M mbs = true.
Proof.
  intros mbs H. unfold hb_mchk in H.
  apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6. repeat (match goal with |- _ /\ _ => split end); assumption.
Qed.

Lemma hb_mwf : forall mbs, hb_mchk mbs = true -> model_wf mbs.
Proof.
  intros mbs H. destruct (hb_mfields mbs H) as (_ & Hn & Hx & Hs & Hd & Hm & _).
  unfold model_wf, model_marks_wf, slots_terminated, NL_SENT_MAX, MARKS_MAX.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  all: intros i Hi; lia.
Qed.

(* the closed facts of the small part: the request (the header's 32 bytes are req_read 2), wk and wa, the windows *)
Lemma hb_tk_chks :
  hb_chk hb_tk_small HB_TK_R hb_tk_req = true /\
  hb_chk hb_tk_small HB_TK_WK (repeat (zb 0) 16) = true /\
  hb_chk hb_tk_small HB_TK_WA (repeat (zb 0) 16) = true /\
  hb_disj hb_tk_shw LA_G_NL NK_SIZE = true /\ hb_wins_ok hb_tk_shw = true /\
  bl_eqb hb_tk_req (map zb [32; 0; 0; 0; 18; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0;
                            0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

Lemma hb_tk_lift : forall kbs w b, hb_tk_small w = Some b -> hb_tk_mem kbs w = Some b.
Proof. intros kbs w b H. unfold hb_tk_mem. rewrite H. reflexivity. Qed.

Lemma hb_tk_sh : forall kbs r s, In r hb_tk_shw -> fst r <= s < fst r + snd r ->
  hb_tk_mem kbs (Z_to_bv 64 s) = Some (zb 0).
Proof.
  intros kbs r s Hr Hs. apply hb_tk_lift. destruct hb_tk_chks as (_ & _ & _ & _ & Hw & _).
  unfold hb_tk_small. rewrite unsigned_lit_small by exact (hb_win_rng hb_tk_shw r s Hw Hr Hs).
  rewrite (hb_sh_in hb_tk_shw r s Hr Hs). reflexivity.
Qed.

Lemma hb_tk_small_gnl : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> hb_tk_small (Z_to_bv 64 a) = None.
Proof.
  intros a Ha. destruct hb_tk_chks as (_ & _ & _ & Hd & _). unfold hb_tk_small.
  rewrite unsigned_lit_small by (unfold LA_G_NL, NK_SIZE in *; lia).
  rewrite (hb_sh_out hb_tk_shw LA_G_NL NK_SIZE a Hd Ha).
  rewrite (hb_inrz_out a HB_TK_M MD_SIZE LA_G_NL NK_SIZE ltac:(vm_compute; reflexivity) Ha).
  rewrite (hb_inrz_out a HB_TK_R 32 LA_G_NL NK_SIZE ltac:(vm_compute; reflexivity) Ha).
  rewrite (hb_inrz_out a HB_TK_WK 40 LA_G_NL NK_SIZE ltac:(vm_compute; reflexivity) Ha).
  rewrite (hb_inrz_out a HB_TK_WA 40 LA_G_NL NK_SIZE ltac:(vm_compute; reflexivity) Ha).
  reflexivity.
Qed.

Lemma hb_tk_mem_gnl : forall kbs i, Z.of_nat (length kbs) = NK_SIZE -> (i < length kbs)%nat ->
  hb_tk_mem kbs (Z_to_bv 64 (LA_G_NL + Z.of_nat i)) = nth_error kbs i.
Proof.
  intros kbs i Hl Hi. unfold hb_tk_mem. rewrite hb_tk_small_gnl by lia. cbv beta iota.
  apply g_mem_at; assumption.
Qed.

Lemma hb_talk_apre_of : forall segs (regs : bvmap 5 word) kbs mbs, hb_kchk kbs = true -> hb_mchk mbs = true ->
  aarg regs 0 = HB_TK_M -> aarg regs 1 = HB_TK_R -> aarg regs 2 = 32 -> aarg regs 3 = HB_TK_WK ->
  aarg regs 4 = 16 -> aarg regs 5 = HB_TK_WA -> aarg regs 6 = 16 -> spZ regs = HB_TK_SP ->
  talk_apre segs regs (hb_tk_mem kbs).
Proof.
  intros segs regs kbs mbs Hk Hm H0 H1 H2 H3 H4 H5 H6 Hsp.
  destruct (hb_kfields kbs Hk) as (Hkl & _).
  destruct (hb_mfields mbs Hm) as (Hml & _ & _ & _ & _ & _ & Hmc).
  destruct hb_tk_chks as (Cr & Ck & Ca & _ & _ & _).
  set (m := hb_tk_mem kbs).
  assert (Lf : forall w b, hb_tk_small w = Some b -> m w = Some b) by (intros w b; apply hb_tk_lift).
  assert (SH : forall r s, In r hb_tk_shw -> fst r <= s < fst r + snd r -> m (Z_to_bv 64 s) = Some (zb 0))
    by (intros r s; apply hb_tk_sh).
  assert (SHn : forall r s, In r hb_tk_shw -> fst r <= s < fst r + snd r -> m (Z_to_bv 64 s) <> None)
    by (intros r s Hr Hs; rewrite (SH r s Hr Hs); discriminate).
  unfold talk_apre, apart_frame. rewrite H0, H1, H2, H3, H4, H5, H6, Hsp, TALK_AK_val.
  exists mbs, kbs, hb_tk_req.
  (* the model block and g_nl *)
  split.
  { split; [|exact Hml]. apply (hb_au8arr segs m HB_TK_M mbs);
      [hb_zle | rewrite Hml; hb_zle | exact (hb_chk_lift _ _ _ _ Lf Hmc)]. }
  split; [exact (hb_mwf mbs Hm)|].
  split.
  { split; [|exact Hkl]. apply (hb_au8arr_fn segs m LA_G_NL kbs);
      [unfold LA_G_NL; lia | rewrite Hkl; unfold LA_G_NL, NK_SIZE; lia |].
    intros i Hi. exact (hb_tk_mem_gnl kbs i Hkl Hi). }
  split; [exact (hb_kwf kbs Hk)|].
  (* the request and the two buffers *)
  split; [exact (proj1 (hb_au8arr segs m HB_TK_R hb_tk_req ltac:(hb_zle) ltac:(hb_zle) (hb_chk_lift _ _ _ _ Lf Cr)))|].
  split; [unfold hb_tk_req; rewrite req_read_len; reflexivity|].
  split; [unfold NL_SENT_LEN; lia|].
  split.
  { intros _ _. exists (repeat (zb 0) 16). split; [reflexivity|].
    apply (hb_au8arr segs m HB_TK_WK); [hb_zle | hb_zle | exact (hb_chk_lift _ _ _ _ Lf Ck)]. }
  split.
  { intros _ _. exists (repeat (zb 0) 16). split; [reflexivity|].
    apply (hb_au8arr segs m HB_TK_WA); [hb_zle | hb_zle | exact (hb_chk_lift _ _ _ _ Lf Ca)]. }
  (* the model block's shadow *)
  split.
  { apply (hb_ra_of segs m HB_TK_M MD_SIZE (fst (hb_win HB_TK_M MD_SIZE)) (snd (hb_win HB_TK_M MD_SIZE)));
      [hb_zle | hb_zle |].
    intros s Hs. apply (SH (hb_win HB_TK_M MD_SIZE) s); [left; reflexivity | exact Hs]. }
  split.
  { apply (hb_hull_of segs m HB_TK_M MD_SIZE (fst (hb_win HB_TK_M MD_SIZE)) (snd (hb_win HB_TK_M MD_SIZE)));
      [hb_zle | hb_zle | hb_zle |].
    intros s Hs. apply (SHn (hb_win HB_TK_M MD_SIZE) s); [left; reflexivity | exact Hs]. }
  split; [unfold amem_range; right; split; hb_zle|].
  (* the chunk queue's shadow *)
  split.
  { apply (hb_ra_of segs m (LA_G_NL + NK_CHUNK) NK_N_CHUNKS (fst (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS))
      (snd (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS))); [hb_zle | hb_zle |].
    intros s Hs. apply (SH (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS) s); [right; left; reflexivity | exact Hs]. }
  split.
  { apply (hb_hull_of segs m (LA_G_NL + NK_CHUNK) NK_N_CHUNKS (fst (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS))
      (snd (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS))); [hb_zle | hb_zle | hb_zle |].
    intros s Hs. apply (SHn (hb_win (LA_G_NL + NK_CHUNK) NK_N_CHUNKS) s); [right; left; reflexivity | exact Hs]. }
  (* the request's shadow and separation *)
  split; [unfold amem_range; right; split; hb_zle|].
  split.
  { apply (hb_ra_of segs m HB_TK_R 32 (fst (hb_win HB_TK_R 32)) (snd (hb_win HB_TK_R 32))); [hb_zle | hb_zle |].
    intros s Hs. apply (SH (hb_win HB_TK_R 32) s); [right; right; left; reflexivity | exact Hs]. }
  split.
  { intros _. apply (hb_hull_of segs m HB_TK_R 32 (fst (hb_win HB_TK_R 32)) (snd (hb_win HB_TK_R 32)));
      [hb_zle | hb_zle | hb_zle |].
    intros s Hs. apply (SHn (hb_win HB_TK_R 32) s); [right; right; left; reflexivity | exact Hs]. }
  split; [unfold apart; hb_or|].
  (* wk and wa *)
  split.
  { intros _ _. split; [unfold apart_gnl; hb_or|]. split; [unfold apart; hb_or|].
    split; [unfold amem_range; right; split; hb_zle|]. split.
    - apply (hb_ra_of segs m HB_TK_WK 16 (fst (hb_win HB_TK_WK 40)) (snd (hb_win HB_TK_WK 40))); [hb_zle | hb_zle |].
      intros s Hs. apply (SH (hb_win HB_TK_WK 40) s); [right; right; right; left; reflexivity | exact Hs].
    - apply (hb_hull_of segs m HB_TK_WK 16 (fst (hb_win HB_TK_WK 40)) (snd (hb_win HB_TK_WK 40)));
        [hb_zle | hb_zle | hb_zle |].
      intros s Hs. apply (SHn (hb_win HB_TK_WK 40) s); [right; right; right; left; reflexivity | exact Hs]. }
  split.
  { intros _ _. split; [unfold apart_gnl; hb_or|]. split; [unfold apart; hb_or|].
    split; [unfold amem_range; right; split; hb_zle|]. split.
    - apply (hb_ra_of segs m HB_TK_WA 16 (fst (hb_win HB_TK_WA 40)) (snd (hb_win HB_TK_WA 40))); [hb_zle | hb_zle |].
      intros s Hs. apply (SH (hb_win HB_TK_WA 40) s); [right; right; right; right; left; reflexivity | exact Hs].
    - apply (hb_hull_of segs m HB_TK_WA 16 (fst (hb_win HB_TK_WA 40)) (snd (hb_win HB_TK_WA 40)));
        [hb_zle | hb_zle | hb_zle |].
      intros s Hs. apply (SHn (hb_win HB_TK_WA 40) s); [right; right; right; right; left; reflexivity | exact Hs]. }
  split; [intros _ _ _ _; unfold apart; hb_or|].
  (* the model block apart from g_nl, and the four ranges apart from talk's window [sp - 4240, sp) *)
  split; [unfold apart_gnl; hb_or|].
  split; [hb_or|].
  split; [hb_or|].
  split; [intros _; hb_or|].
  intros _; hb_or.
Qed.

Definition hb_tk_memc : word -> option byte := hb_tk_mem hb_kbs.

(* the Pre lambda of talk_acontract holds at hb_tk_memc, for every segment list, at every register file with
   a0 = M, a1 = R, a2 = 32, a3 = WK, a4 = 16, a5 = WA, a6 = 16 and sp = model_read's realigned sp *)
Lemma hb_talk_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = HB_TK_M -> aarg regs 1 = HB_TK_R -> aarg regs 2 = 32 -> aarg regs 3 = HB_TK_WK ->
  aarg regs 4 = 16 -> aarg regs 5 = HB_TK_WA -> aarg regs 6 = 16 -> spZ regs = HB_TK_SP ->
  talk_apre segs regs hb_tk_memc.
Proof.
  intros segs regs H0 H1 H2 H3 H4 H5 H6 Hsp.
  exact (hb_talk_apre_of segs regs hb_kbs hb_tk_mbs hb_kchk_ok hb_mchk_ok H0 H1 H2 H3 H4 H5 H6 Hsp).
Qed.

(* ==========================================================================
   3. text_of, called by LLVMFuzzerTestOneInput at 0x82e24, input 04 05 00
   ========================================================================== *)

(* LLVMFuzzerTestOneInput's realigned sp, the cursor and *own slots of its real frame, the input block *)
Definition HB_TX_S1 : Z := 0x7ffffffeee60.
Definition HB_TX_P : Z := HB_TX_S1 + 0x118.
Definition HB_TX_O : Z := HB_TX_S1 + 0x130.
Definition HB_TX_D : Z := 0x602000000010.

(* [p, p + 32): the cursor (d + 1, 2), the slot s1 + 0x128 (residue 0), *own (residue 0) *)
Definition hb_tx_stk : list byte := wle_bytes 8 (HB_TX_D + 1) ++ wle_bytes 8 2 ++ repeat (zb 0) 16.
Definition hb_tx_inp : list byte := map zb [4; 5; 0].

(* texts[i] and its string, from the pin *)
Definition hb_texts : list (Z * list byte) :=
  [(0x20fc0, []);
   (0x21100, map zb [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100]);     (* reac-pw:served *)
   (0x21120, map zb [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100]);     (* reac-pw:minted *)
   (0x21140, map zb [104; 111; 115; 116; 45; 97; 108; 105; 97; 115]);                         (* host-alias *)
   (0x21160, map zb [114; 101; 97; 99; 45; 112; 119; 58]);                                    (* reac-pw: *)
   (0x21180, map zb [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 50]); (* reac-pw:served2 *)
   (0x211a0, map zb [114; 101; 97; 99; 45; 112; 119]);                                        (* reac-pw *)
   (0x211c0, map zb [118; 108; 97; 110]);                                                     (* vlan *)
   (0x211e0, map zb [118; 101; 116; 104]);                                                    (* veth *)
   (0x21200, map zb [118; 108; 97; 110; 120]);                                                (* vlanx *)
   (0x21220, map zb [118; 108; 97])].                                                         (* vla *)
Definition hb_tx_tab : list byte := flat_map (fun e => wle_bytes 8 (fst e)) hb_texts.

Fixpoint hb_str_at (l : list (Z * list byte)) (a : Z) : option byte :=
  match l with
  | [] => None
  | (q, s) :: t =>
      if inrz a q (Z.of_nat (length s) + 1) then nth_error (s ++ [zb 0]) (Z.to_nat (a - q)) else hb_str_at t a
  end.

Definition hb_tx_shw : list (Z * Z) := [hb_win HB_TX_P 32; hb_win LA_TEXTS 88; hb_win HB_TX_D 3].

Definition hb_tx_mem (w : word) : option byte :=
  if bv_unsigned w =? SHADOW_OFF + HB_TX_D / 8 then Some (zb 3)
  else if hb_sh hb_tx_shw (bv_unsigned w) then Some (zb 0)
  else if inrz (bv_unsigned w) HB_TX_P 32 then nth_error hb_tx_stk (Z.to_nat (bv_unsigned w - HB_TX_P))
  else if inrz (bv_unsigned w) HB_TX_D 3 then nth_error hb_tx_inp (Z.to_nat (bv_unsigned w - HB_TX_D))
  else if inrz (bv_unsigned w) LA_TEXTS 88 then nth_error hb_tx_tab (Z.to_nat (bv_unsigned w - LA_TEXTS))
  else hb_str_at hb_texts (bv_unsigned w).

(* entry j of the table: the pointer, the string and its NUL, no NUL inside, the bounds *)
Definition hb_tx_ent_ok (j : nat) : bool :=
  let e := nth j hb_texts (0, []) in
  hb_vchk hb_tx_mem (LA_TEXTS + 8 * Z.of_nat j) 8 (fst e)
  && hb_chk hb_tx_mem (fst e) (snd e ++ [zb 0])
  && negb (existsb (fun b => bv_unsigned b =? 0) (snd e))
  && (Z.of_nat (length (snd e)) <? 320)
  && (0 <? fst e)
  && (fst e + Z.of_nat (length (snd e)) + 1 <=? LA_TEXTS).

Lemma hb_tx_chks :
  hb_vchk hb_tx_mem HB_TX_P 8 (HB_TX_D + 1) = true /\
  hb_vchk hb_tx_mem (HB_TX_P + 8) 8 2 = true /\
  hb_vchk hb_tx_mem (HB_TX_O - 16) 8 2 = true /\
  hb_chk hb_tx_mem HB_TX_P (firstn 16 hb_tx_stk) = true /\
  hb_chk hb_tx_mem HB_TX_O (repeat (zb 0) 8) = true /\
  hb_chk hb_tx_mem (HB_TX_O - 16) (wle_bytes 8 2 ++ repeat (zb 0) 8) = true /\
  hb_chk hb_tx_mem (HB_TX_D + 1) (map zb [5; 0]) = true /\
  hb_oeq (hb_tx_mem (Z_to_bv 64 (SHADOW_OFF + HB_TX_D / 8))) (Some (zb 3)) = true /\
  hb_wins_ok hb_tx_shw = true /\
  forallb hb_tx_ent_ok (seq 0 11) = true.
Proof. repeat (match goal with |- _ /\ _ => split end); vm_compute; reflexivity. Qed.

Lemma hb_tx_sh : forall r s, In r hb_tx_shw -> fst r <= s < fst r + snd r -> hb_tx_mem (Z_to_bv 64 s) <> None.
Proof.
  intros r s Hr Hs. destruct hb_tx_chks as (_ & _ & _ & _ & _ & _ & _ & _ & Hw & _).
  unfold hb_tx_mem. rewrite unsigned_lit_small by exact (hb_win_rng hb_tx_shw r s Hw Hr Hs).
  destruct (s =? SHADOW_OFF + HB_TX_D / 8); [cbv beta iota; discriminate|].
  rewrite (hb_sh_in hb_tx_shw r s Hr Hs). cbv beta iota. discriminate.
Qed.

Lemma hb_tx_sh0 : forall r s, In r hb_tx_shw -> fst r <= s < fst r + snd r ->
  inrz (SHADOW_OFF + HB_TX_D / 8) (fst r) (snd r) = false -> hb_tx_mem (Z_to_bv 64 s) = Some (zb 0).
Proof.
  intros r s Hr Hs Hg. destruct hb_tx_chks as (_ & _ & _ & _ & _ & _ & _ & _ & Hw & _).
  pose proof (hb_inrz_ne _ _ _ s Hg Hs) as Hn. apply Z.eqb_neq in Hn.
  unfold hb_tx_mem. rewrite unsigned_lit_small by exact (hb_win_rng hb_tx_shw r s Hw Hr Hs).
  rewrite Hn, (hb_sh_in hb_tx_shw r s Hr Hs). reflexivity.
Qed.

(* the facts of the instance the table conjunct needs: each string and its NUL are `text_of_ro` *)
Definition hb_tx_ro (segs : list Segment) (rlo rhi : Z) (B : asyms) : Prop :=
  Forall (fun e => text_of_ro segs rlo rhi B (fst e) (Z.of_nat (length (snd e)) + 1)) hb_texts.

(* the Pre lambda of text_of_acontract holds at hb_tx_mem, for every segment list, relro bounds and asyms whose
   errno lies below kLowMemEnd (HERR) and that make the 11 strings read-only image (hb_tx_ro) and the malloc trace a
   wild prefix (text_of_traces), at every register file with a0 = p, a1 = o and sp = s1 *)
Lemma hb_text_of_apre_sat : forall segs rlo rhi B (regs : bvmap 5 word)
  (HERR : 0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd),
  hb_tx_ro segs rlo rhi B -> text_of_traces B ->
  aarg regs 0 = HB_TX_P -> aarg regs 1 = HB_TX_O -> spZ regs = HB_TX_S1 ->
  text_of_apre segs rlo rhi B regs hb_tx_mem.
Proof.
  intros segs rlo rhi B regs HERR Hro Htr H0 H1 Hsp.
  destruct hb_tx_chks as (Vc0 & Vc1 & Vw & Cp & Co & Cu & Ci & Cg & _ & Ce).
  unfold text_of_apre, apart_frame. rewrite H0, H1, Hsp, TEXT_OF_AK_val.
  exists (HB_TX_D + 1), 2, (map zb [5; 0]).
  (* the cursor *)
  split; [exact (hb_val_mem segs hb_tx_mem HB_TX_P 8 (HB_TX_D + 1) Vc0)|].
  split; [exact (hb_val_mem segs hb_tx_mem (HB_TX_P + 8) 8 2 Vc1)|].
  split; [split; [hb_zle | hb_zlt]|].
  split; [split; [hb_zle | hb_zlt]|].
  split.
  { exists (firstn 16 hb_tx_stk). split; [reflexivity|].
    apply (hb_au8arr segs hb_tx_mem HB_TX_P); [hb_zle | hb_zle | exact Cp]. }
  split; [vm_compute; reflexivity|].
  split.
  { apply (hb_ra_of segs hb_tx_mem HB_TX_P 16 (fst (hb_win HB_TX_P 32)) (snd (hb_win HB_TX_P 32)));
      [hb_zle | hb_zle |].
    intros s Hs. apply (hb_tx_sh0 (hb_win HB_TX_P 32) s); [left; reflexivity | exact Hs | vm_compute; reflexivity]. }
  (* amem_range p 16: p is in high memory *)
  split; [right; split; hb_zle|].
  split; [hb_or|].
  (* *own *)
  split.
  { exists (repeat (zb 0) 8). split; [reflexivity|].
    apply (hb_au8arr segs hb_tx_mem HB_TX_O); [hb_zle | hb_zle | exact Co]. }
  split.
  { apply (hb_ra_of segs hb_tx_mem HB_TX_O 8 (fst (hb_win HB_TX_P 32)) (snd (hb_win HB_TX_P 32)));
      [hb_zle | hb_zle |].
    intros s Hs. apply (hb_tx_sh0 (hb_win HB_TX_P 32) s); [left; reflexivity | exact Hs | vm_compute; reflexivity]. }
  (* amem_range o 8: o is in high memory *)
  split; [right; split; hb_zle|].
  (* shadow_hull_vis o 8: the same shadow window holds every byte of the hull *)
  split.
  { apply (hb_hull_of segs hb_tx_mem HB_TX_O 8 (fst (hb_win HB_TX_P 32)) (snd (hb_win HB_TX_P 32)));
      [hb_zle | hb_zle | hb_zle |].
    intros s Hs. rewrite (hb_tx_sh0 (hb_win HB_TX_P 32) s); [discriminate | left; reflexivity | exact Hs |
      vm_compute; reflexivity]. }
  split; [hb_or|].
  split; [unfold apart; hb_or|].
  (* errno: the cursor is above kLowMemEnd, errno below it (HERR) *)
  split; [unfold apart; left; apply (Z.le_trans _ kLowMemEnd); [exact (proj2 HERR) | hb_zle]|].
  (* the input bytes left *)
  split; [exact (proj1 (hb_au8arr segs hb_tx_mem (HB_TX_D + 1) (map zb [5; 0]) ltac:(hb_zle) ltac:(hb_zle) Ci))|].
  split; [reflexivity|].
  split.
  { apply (hb_ra_part segs hb_tx_mem HB_TX_D 3 (HB_TX_D + 1) 2); [vm_compute; reflexivity | lia | lia | lia |].
    exact (hb_oeq_ok _ _ Cg). }
  split.
  { intros _. split.
    { apply (hb_hull_of segs hb_tx_mem (HB_TX_D + 1) 2 (fst (hb_win HB_TX_D 3)) (snd (hb_win HB_TX_D 3)));
        [lia | hb_zle | hb_zle |].
      intros s Hs. apply (hb_tx_sh (hb_win HB_TX_D 3) s); [right; right; left; reflexivity | exact Hs]. }
    split; [unfold amem_range; right; split; hb_zle|].
    split; [hb_or|].
    split; [unfold apart; hb_or|].
    split; [unfold apart; hb_or|].
    hb_zle. }
  (* the words malloc's unwinder reads under *own: [o - 16] = [p + 8] = 2, [o - 8] = 0 *)
  split.
  { intros i Hi. apply (hb_chk_some segs hb_tx_mem (HB_TX_O - 16) _ i Cu).
    replace (Z.of_nat (length (wle_bytes 8 2 ++ repeat (zb 0) 8))) with 16 by reflexivity. exact Hi. }
  split.
  { intros w Hw Rw.
    rewrite (hb_u64_unique segs hb_tx_mem (HB_TX_O - 16) 2 w (hb_val_mem segs hb_tx_mem (HB_TX_O - 16) 8 2 Vw)
               Hw ltac:(lia) Rw).
    hb_zle. }
  (* the table and its strings *)
  split.
  { apply (hb_ra_of segs hb_tx_mem LA_TEXTS (8 * TEXTS_N) (fst (hb_win LA_TEXTS 88)) (snd (hb_win LA_TEXTS 88)));
      [hb_zle | hb_zle |].
    intros s Hs.
    apply (hb_tx_sh0 (hb_win LA_TEXTS 88) s); [right; left; reflexivity | exact Hs | vm_compute; reflexivity]. }
  split; [unfold apart; hb_or|].
  split; [unfold apart; hb_or|].
  split.
  { intros i Hi. unfold TEXTS_N in Hi.
    rewrite forallb_forall in Ce. pose proof (Ce (Z.to_nat i) ltac:(apply in_seq; lia)) as Ej.
    replace i with (Z.of_nat (Z.to_nat i)) by lia.
    unfold hb_tx_ent_ok in Ej. cbv zeta in Ej.
    revert Ej. destruct (nth (Z.to_nat i) hb_texts (0, [])) as [q s] eqn:Ne. intros Ej. cbn [fst snd] in Ej.
    apply andb_prop in Ej as [Ej E6]. apply andb_prop in Ej as [Ej E5]. apply andb_prop in Ej as [Ej E4].
    apply andb_prop in Ej as [Ej E3]. apply andb_prop in Ej as [E1 E2].
    apply Z.leb_le in E6. apply Z.ltb_lt in E5, E4. apply negb_true_iff in E3.
    unfold LA_TEXTS in E6.
    exists q, s.
    split; [exact (hb_val_mem segs hb_tx_mem _ 8 q E1)|].
    split; [lia|].
    split.
    { split.
      - apply (proj1 (hb_au8arr segs hb_tx_mem q (s ++ [zb 0]) ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia) E2)).
      - intros Hin.
        assert (X : existsb (fun b => bv_unsigned b =? 0) s = true)
          by (apply existsb_exists; exists (zb 0); split; [exact Hin | reflexivity]).
        congruence. }
    split; [exact E4|].
    split.
    { unfold hb_tx_ro in Hro. rewrite Forall_forall in Hro. apply (Hro (q, s)). rewrite <- Ne. apply nth_In.
      change (length hb_texts) with 11%nat. lia. }
    split; unfold apart; right; unfold HB_TX_P, HB_TX_O, HB_TX_S1; lia. }
  exact Htr.
Qed.

Print Assumptions hb_talk_apre_sat.
Print Assumptions hb_text_of_apre_sat.
