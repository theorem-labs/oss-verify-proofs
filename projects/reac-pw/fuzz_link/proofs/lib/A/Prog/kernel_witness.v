(* Satisfiability witnesses of the function-specific Pre of the seven image-A contracts
   (fuzz_socket_c.v, fuzz_send_c.v, fuzz_recv_c.v, fuzz_if_nametoindex_c.v, kernel_c.v, attr_text_c.v,
   nl_error_c.v), in the style of form_witness.v: each `<f>_apre_sat` says that `<f>_apre` holds, for every segment
   list, at a concrete memory that holds the values a real run holds at the call. The journal part of each Pre
   (link_amem.v `apre`, and for an `aleaf_rd` contract the `akb` premise on its read set) needs AR of image A's
   start state, which the start-up files give; it is written out in each contract file's
   header. Each memory holds every byte the Pre reads, so no ROM byte is read.

   THE RUN (kernel_c.v's witness run). LLVMFuzzerTestOneInput (0x827d4) on the 13-byte input
   00 00 10 10 00 00 00 01 00 01 00 01 04: memset of g_nl and interfaces() (fuzz_link.c:769-770: if_name[j] =
   g_names[k], k = j + j / 15, if_index[j] = k + 2 for j < 60; odd[1..4], index 101..104 for j = 60..63;
   n_if = 64); op 0 = op_read: name byte 0 = g_names[0] = "nl0", kind cap and alias cap 16; kernel(in) at 0x82ec0:
   flags 0, both errno bytes 0 (nl_errno 105), one chunk, mode 0, one message of kind 0 (RTM_NEWLINK) with one
   attribute, a = 4: attr_text(w2, 3, "x", 0), so chunk 0 is the 40 bytes 28 00 00 00 10 00 00 00 01 00 00 00
   00 00 00 00, 16 zero bytes, 06 00 03 00 78 00 00 00; then reac_link_alias_read("nl0", ...) (0x8867c) calls
   fuzz_if_nametoindex (index 2), builds the 32-byte RTM_GETLINK request in its class-1 side frame F1 at F1 + 0x20
   (listing +0x180..+0x1c0: 20 00 00 00 12 00 01 00 01 00 00 00, 8 zero bytes, index 2, 8 zero bytes) and calls
   nl_talk(F1 + 0x20, 32, ...), which calls fuzz_socket, fuzz_send(7, F1 + 0x20, 32) and
   fuzz_recv(7, F9 + 0x20, 0x4000) (F9 = its class-9 side frame; nl_talk +0x1d4 `addi s10, s2, 0x20`, +0x1ec
   `lui a2, 4`). nl_error's witness is the same run with the kind byte 1 (input 00 00 10 10 00 00 00 01 00 01 01:
   kernel +0x6d0 calls nl_error(w2, 0, -1) on the w2 it has just zeroed).

   Addresses: sp of LLVMFuzzerTestOneInput at its calls = its s1 = KW_SP (kernel_c.v); reac_link_alias_read's
   realigned sp RA_SP = KW_SP - 0x80; nl_talk's NT_SP = RA_SP - 0xc0; kernel's s1 = KN_SP = KW_SP - 0x160 (all
   32-aligned, on the real stack). Side frames: frame_addr ly c 0 = ly_F + fs_frame_off c 0 with ly_F = W_LYF
   ([INFERENCE] the start-up lane fixes ly_F; any mmap address in high memory gives the same facts); kernel's w2 is
   its class-8 frame + 0x1130 (kernel +0x4dc). errno at TFIB_ERRNO 0x631b6c = TFIB_TP 0x631c10 - 164
   (lib/A/AF0m.v:16-21), value 0 ([INFERENCE]). The .rodata objects and the texts table at the addresses of
   kernel_c.v's header (read from the pin); each string in its 32-byte instrumented slot, the rest of the slot 0.
   Shadow: every shadow byte a Pre reads is given as 0 over the hull of the range, padded by 64 bytes on each side
   (zsh). In the run the last granule of an object has its partial count and the redzones after it their poison;
   the Pre asks only that the named ranges be addressable and their hulls visible, which both give.

   The memories (each lemma states the argument registers and sp it needs):
   - fs_mem, fuzz_socket at nl_talk +0x1b0 (0x88b24): g_nl G1 (after kernel: the table, chunk 0, chunk_len[0] = 40,
     n_chunks 1, next 0, end_errno 105, socket_errno = send_errno = 0, open = opened = closed = misuse = 0,
     n_sent 0); errno; its shadow.
   - fd_mem, fuzz_send at nl_talk +0x1c8 (0x88b3c): g_nl G2 = G1 with open 1, opened 1; the request at F1 + 0x20;
     the shadow of g_nl, errno and the request.
   - fr_mem, fuzz_recv at nl_talk +0x200 (0x88b74): g_nl G3 = G2 with sent[0] = the request, sent_len[0] = 32,
     n_sent 1; the 16384 bytes of nl_talk's receive buffer, 0 ([INFERENCE] a fresh side frame); the shadow of
     g_nl, errno and the buffer (meta_fill_00 at nl_talk +0x1e8 has just cleared the buffer's).
   - fi_mem, fuzz_if_nametoindex at reac_link_alias_read +0x174 (0x887f0), a0 = g_names[0]: g_nl G1; g_names (the
     64 names "nl<k>", NUL-padded to 8); the four odd strings; their shadow and g_nl's.
   - kw_mem, kernel at LLVMFuzzerTestOneInput +0x6ec (0x82ec0): g_nl G0 (memset and interfaces() only); g_names;
     long_alias and the 3 bytes after it, 0; the .rodata objects (.str.1, odd[1..4], nl_errno.e, .str.8,
     msg_build.codes, texts[1..10]); the texts table; the cursor (KW_IN + 4, 9) at KW_CUR = KW_SP + 0x118 in
     LLVMFuzzerTestOneInput's real frame; the 13 input bytes at KW_IN (the driver's heap copy); their shadow.
   - at_mem, attr_text at kernel +0xb40 (0x84870): w2's 4112 bytes (nlmsghdr of type 16 and seq 1, 16 zero bytes,
     zeros to 4096, n = 32, full = 0); the .rodata objects ("x" at 0x210c0); their shadow.
   - ne_mem, nl_error at kernel +0x1b7c (0x858ac): w2's 4112 bytes, 0 (n = 0, full = 0); its shadow.

   How the lemmas are proved: a memory is a list of regions (`wmem`), g_nl's first. `anlk_at`, which names all
   271992 bytes of g_nl, is `gbs_anlk`, proved over an abstract byte function; every other fact (nlk_wf and the
   fields of the state, the table, the strings, the shadow, the separations) is one boolean computed by vm_compute,
   with a soundness lemma per checker (`wc_*`), so no tactic but vm_compute sees the list. The register names in
   each lemma are the arguments and sp the Pre reads.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem form_witness.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
fuzz_socket_c fuzz_send_c fuzz_recv_c fuzz_if_nametoindex_c kernel_c attr_text_c nl_error_c.
Import ListNotations.
Local Open Scope Z_scope.
(* No lia of this file needs division equations (each division is an atom whose facts the proof states); the value
   the kit's files leave (true) makes every lia here slow. Restored at the end of the file. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ==========================================================================
   0. A witness memory: a list of regions; the first region that holds an address gives its byte
   ========================================================================== *)

Definition wreg : Type := (Z * Z * (Z -> option byte))%type.
Fixpoint wlook (rs : list wreg) (z : Z) : option byte :=
  match rs with
  | [] => None
  | (lo, n, f) :: t => if inrz z lo n then f (z - lo) else wlook t z
  end.
Definition wmem (rs : list wreg) : word -> option byte := fun w => wlook rs (bv_unsigned w).

Lemma wmem_lit : forall rs z, 0 <= z < 2 ^ 64 -> wmem rs (Z_to_bv 64 z) = wlook rs z.
Proof. intros rs z Hz. unfold wmem. rewrite unsigned_lit_small by exact Hz. reflexivity. Qed.

Lemma wmem_mbyte : forall segs rs z b, 0 <= z < 2 ^ 64 -> wlook rs z = Some b -> mbyte segs (wmem rs) z = Some b.
Proof. intros segs rs z b Hz Hb. unfold mbyte. rewrite (wmem_lit rs z Hz), Hb. reflexivity. Qed.

Lemma wmem_writable : forall segs rs z b, 0 <= z < 2 ^ 64 -> wlook rs z = Some b -> writable_at segs (wmem rs) z.
Proof. intros segs rs z b Hz Hb. unfold writable_at, wview. rewrite (wmem_lit rs z Hz), Hb. cbv beta iota. discriminate. Qed.

Definition oeqb (o : option byte) (b : byte) : bool := match o with Some c => bz c =? bz b | None => false end.
Lemma oeqb_true : forall o b, oeqb o b = true -> o = Some b.
Proof. intros [c|] b H; [|discriminate]. cbn [oeqb] in H. apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H. Qed.

(* the bytes l at a *)
Fixpoint wc_go (rs : list wreg) (a : Z) (l : list byte) : bool :=
  match l with [] => true | b :: t => oeqb (wlook rs a) b && wc_go rs (a + 1) t end.
Lemma wc_go_ok : forall rs l a, wc_go rs a l = true ->
  forall i, (i < length l)%nat -> wlook rs (a + Z.of_nat i) = nth_error l i.
Proof.
  intros rs l. induction l as [|b t IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
  cbn [wc_go] in H. apply andb_true_iff in H as [H1 H2].
  destruct i as [|i].
  - change (nth_error (b :: t) 0) with (Some b). replace (a + Z.of_nat 0) with a by lia. exact (oeqb_true _ _ H1).
  - change (nth_error (b :: t) (S i)) with (nth_error t i).
    replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia. apply IH; [exact H2 | lia].
Qed.
Definition wc_bytes (rs : list wreg) (a : Z) (l : list byte) : bool :=
  (0 <=? a) && (a + Z.of_nat (length l) <=? 2 ^ 64) && wc_go rs a l.
Lemma wc_bytes_ok : forall segs rs a l, wc_bytes rs a l = true -> abytes segs (wmem rs) a l.
Proof.
  intros segs rs a l H. unfold wc_bytes in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [exact H1|]. split; [exact H2|].
  intros i Hi. pose proof (wc_go_ok rs l a H3 i Hi) as E.
  destruct (nth_error l i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  apply wmem_mbyte; [lia | exact E].
Qed.

(* n present (so writable) bytes at a *)
Fixpoint wc_some (rs : list wreg) (a : Z) (k : nat) : bool :=
  match k with O => true | S k' => (if wlook rs a then true else false) && wc_some rs (a + 1) k' end.
Lemma wc_some_ok : forall rs k a, wc_some rs a k = true ->
  forall i, 0 <= i < Z.of_nat k -> exists b, wlook rs (a + i) = Some b.
Proof.
  intros rs k. induction k as [|k IH]; intros a H i Hi; [lia|].
  cbn [wc_some] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. destruct (wlook rs a) as [b|]; [exists b; reflexivity | discriminate].
  - replace (a + i) with ((a + 1) + (i - 1)) by lia. apply IH; [exact H2 | lia].
Qed.
Definition wc_wr (rs : list wreg) (a n : Z) : bool := (0 <=? a) && (a + n <=? 2 ^ 64) && wc_some rs a (Z.to_nat n).
Lemma wc_wr_ok : forall segs rs a n, wc_wr rs a n = true -> awrange segs (wmem rs) a n.
Proof.
  intros segs rs a n H. unfold wc_wr in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  intros i Hi. destruct (wc_some_ok rs (Z.to_nat n) a H3 i ltac:(lia)) as [b Hb].
  apply (wmem_writable segs rs (a + i) b); [lia | exact Hb].
Qed.
Definition wc_u8 (rs : list wreg) (a : Z) (l : list byte) : bool := wc_bytes rs a l && wc_wr rs a (Z.of_nat (length l)).
Lemma wc_u8_ok : forall segs rs a l, wc_u8 rs a l = true -> au8arr segs (wmem rs) a l.
Proof.
  intros segs rs a l H. apply andb_true_iff in H as [H1 H2].
  split; [exact (wc_bytes_ok segs rs a l H1) | exact (wc_wr_ok segs rs a _ H2)].
Qed.

(* range_addressable, through zero shadow bytes: every shadow byte from that of a to that of a + n - 1 is 0, so each
   byte of [a, a + n) passes the check (saddr_ok's s = 0). The walk steps through the shadow bytes, so it divides
   only twice (a per-byte shadow_addr costs a Z division in the VM for each of g_nl's 271992 bytes). *)
Fixpoint wc_zgo (rs : list wreg) (s : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => (match wlook rs s with Some b => bz b =? 0 | None => false end) && wc_zgo rs (s + 1) k'
  end.
Lemma wc_zgo_ok : forall rs k s0, wc_zgo rs s0 k = true -> forall s, s0 <= s < s0 + Z.of_nat k ->
  exists b, wlook rs s = Some b /\ bz b = 0.
Proof.
  intros rs k. induction k as [|k IH]; intros s0 H s Hs; [lia|].
  cbn [wc_zgo] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec s s0) as [->|Hne].
  - revert H1. destruct (wlook rs s0) as [b|]; intros H1; [|discriminate].
    exists b. split; [reflexivity | apply Z.eqb_eq; exact H1].
  - apply (IH (s0 + 1) H2). lia.
Qed.
Definition wc_ra (rs : list wreg) (a n : Z) : bool :=
  (0 <=? shadow_addr a) && (shadow_addr (a + n - 1) <? 2 ^ 64) &&
  wc_zgo rs (shadow_addr a) (Z.to_nat (shadow_addr (a + n - 1) - shadow_addr a + 1)).
Lemma wc_ra_ok : forall segs rs a n, wc_ra rs a n = true -> range_addressable (ard segs (wmem rs)) SHADOW_OFF a n.
Proof.
  intros segs rs a n H x Hx. unfold wc_ra in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  assert (M1 : shadow_addr a <= shadow_addr x) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (M2 : shadow_addr x <= shadow_addr (a + n - 1))
    by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  destruct (wc_zgo_ok rs _ _ H3 (shadow_addr x) ltac:(lia)) as (b & Hb & Hz).
  exists 0. split; [|left; reflexivity].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). unfold ard.
  rewrite (wmem_mbyte segs rs (shadow_addr x) b ltac:(lia) Hb). cbn [option_map]. f_equal. exact Hz.
Qed.

(* shadow_hull_vis: every shadow byte of the 8-aligned hull is present *)
Definition wc_hull (rs : list wreg) (x n : Z) : bool :=
  let lo := shadow_addr x / 8 * 8 in let hi := shadow_addr (x + n - 1) / 8 * 8 + 8 in
  (0 <=? lo) && (hi <=? 2 ^ 64) && wc_some rs lo (Z.to_nat (hi - lo)).
Lemma wc_hull_ok : forall segs rs x n, wc_hull rs x n = true -> shadow_hull_vis (ard segs (wmem rs)) x n.
Proof.
  intros segs rs x n H s Hs. cbv beta zeta delta [wc_hull] in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (wc_some_ok rs _ _ H3 (s - shadow_addr x / 8 * 8) ltac:(lia)) as [b Hb].
  replace (shadow_addr x / 8 * 8 + (s - shadow_addr x / 8 * 8)) with s in Hb by lia.
  unfold ard. rewrite (wmem_mbyte segs rs s b ltac:(lia) Hb). discriminate.
Qed.

(* the bytes after e to the end of e's 8-byte granule are present (atail_vis, lib/A/Rt/RtDefs.v:54-55, over `ard`) *)
Definition wc_tail (rs : list wreg) (e : Z) : bool :=
  let hi := e - e mod 8 + 8 in
  (0 <=? e + 1) && (hi <=? 2 ^ 64) && wc_some rs (e + 1) (Z.to_nat (hi - (e + 1))).
Lemma wc_tail_ok : forall segs rs e, wc_tail rs e = true ->
  forall a, e < a < e - e mod 8 + 8 -> ard segs (wmem rs) a <> None.
Proof.
  intros segs rs e H a Ha. cbv beta zeta delta [wc_tail] in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  remember (e - e mod 8 + 8) as hi eqn:Ehi. clear Ehi.
  destruct (wc_some_ok rs _ _ H3 (a - (e + 1)) ltac:(lia)) as [b Hb].
  replace (e + 1 + (a - (e + 1))) with a in Hb by lia.
  unfold ard. rewrite (wmem_mbyte segs rs a b ltac:(lia) Hb). discriminate.
Qed.

(* little-endian values (val_mem, au32_at, au64_at) *)
Lemma nth_error_seq0 : forall n s k, (k < n)%nat -> nth_error (seq s n) k = Some (s + k)%nat.
Proof.
  induction n as [|n IH]; intros s k Hk; [lia|].
  destruct k as [|k]; cbn [seq nth_error]; [f_equal; lia|]. rewrite IH by lia. f_equal; lia.
Qed.
Definition vbytes (v : Z) (n : nat) : list byte := map (fun k => Z_to_bv 8 (YO0f.le_byte v n k)) (seq 0 n).
Lemma length_vbytes : forall v n, length (vbytes v n) = n.
Proof. intros v n. unfold vbytes. rewrite length_map, length_seq. reflexivity. Qed.
Definition wc_val (rs : list wreg) (a : Z) (n : nat) (v : Z) : bool := wc_bytes rs a (vbytes v n).
Lemma wc_val_ok : forall segs rs a n v, wc_val rs a n v = true -> val_mem segs (wmem rs) a n v.
Proof.
  intros segs rs a n v H k Hk. destruct (wc_bytes_ok segs rs a _ H) as (_ & _ & Hb).
  rewrite (Hb k ltac:(rewrite length_vbytes; exact Hk)). unfold vbytes.
  rewrite nth_error_map, nth_error_seq0 by exact Hk. reflexivity.
Qed.

(* C strings *)
Definition wc_cstr (rs : list wreg) (p : Z) (s : list byte) : bool :=
  wc_bytes rs p (s ++ [zb 0]) && forallb (fun b => negb (bz b =? 0)) s.
Lemma wc_cstr_ok : forall segs rs p s, wc_cstr rs p s = true -> acstr_at segs (wmem rs) p s.
Proof.
  intros segs rs p s H. unfold wc_cstr in H. apply andb_true_iff in H as [H1 H2].
  split; [exact (wc_bytes_ok segs rs p _ H1)|].
  intros Hin. rewrite forallb_forall in H2. specialize (H2 _ Hin). vm_compute in H2. discriminate.
Qed.

(* the Z-only premises *)
Definition amrb (p n : Z) : bool :=
  (p + n <=? kLowMemEnd - 1) || ((kHighMemBeg <=? p) && (p + n <=? kHighMemEnd - 1)).
Lemma amrb_ok : forall p n, amrb p n = true -> amem_range p n.
Proof.
  intros p n H. unfold amrb in H. unfold amem_range. apply orb_true_iff in H as [H|H].
  - left. apply Z.leb_le. exact H.
  - apply andb_true_iff in H as [H1 H2]. right. split; apply Z.leb_le; assumption.
Qed.
Definition apartb (a n b k : Z) : bool := (a + n <=? b) || (b + k <=? a).
Lemma apartb_ok : forall a n b k, apartb a n b k = true -> apart a n b k.
Proof. intros a n b k H. unfold apartb in H. unfold apart. apply orb_true_iff in H as [H|H]; [left|right]; apply Z.leb_le; exact H. Qed.
Lemma apgb_ok : forall g a n, apartb a n g NK_SIZE = true -> apart_gnl g a n.
Proof. intros g a n H. exact (apartb_ok a n g NK_SIZE H). Qed.
Lemma apart_frame_of : forall regs sp K a n, spZ regs = sp -> apartb a n (sp - K) K = true -> apart_frame regs K a n.
Proof. intros regs sp K a n Hsp H. apply apartb_ok in H. unfold apart in H. unfold apart_frame. rewrite Hsp. lia. Qed.

(* the two well-formedness relations, as booleans *)
Lemma forallb_nat : forall (f : nat -> bool) n, forallb f (seq 0 n) = true -> forall j, (j < n)%nat -> f j = true.
Proof. intros f n H j Hj. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Definition nlk_wfb (bs : list byte) : bool :=
  (0 <=? nk_n_chunks bs) && (nk_n_chunks bs <=? NL_CHUNKS) &&
  (0 <=? nk_next bs) && (nk_next bs <=? nk_n_chunks bs) &&
  (0 <=? nk_n_sent bs) && (nk_n_sent bs <=? NL_SENT_MAX) &&
  (0 <=? nk_n_if bs) && (nk_n_if bs <=? 80) &&
  (0 <=? nk_open bs) && (nk_open bs <=? 1) &&
  (0 <=? nk_opened bs) && (nk_opened bs <? 2 ^ 31) &&
  (0 <=? nk_closed bs) && (nk_closed bs <? 2 ^ 31) &&
  (0 <=? nk_misuse bs) && (nk_misuse bs <=? 1) &&
  (0 <=? nk_end_errno bs) && (nk_end_errno bs <? 2 ^ 31) &&
  (0 <=? nk_socket_errno bs) && (nk_socket_errno bs <? 2 ^ 31) &&
  (0 <=? nk_send_errno bs) && (nk_send_errno bs <? 2 ^ 31) &&
  forallb (fun j => let v := fld_u64 bs (NK_CHUNK_LEN + 8 * Z.of_nat j) in (0 <=? v) && (v <=? NL_CHUNK_MAX))
    (seq 0 (Z.to_nat (nk_n_chunks bs))) &&
  forallb (fun j => let v := fld_u64 bs (NK_SENT_LEN + 8 * Z.of_nat j) in (0 <=? v) && (v <=? NL_SENT_LEN))
    (seq 0 (Z.to_nat (nk_n_sent bs))).
Lemma nlk_wfb_ok : forall bs, nlk_wfb bs = true -> nlk_wf bs.
Proof.
  intros bs H. unfold nlk_wfb in H. repeat rewrite andb_true_iff in H.
  repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end.
  repeat match goal with
  | Hx : (_ <=? _) = true |- _ => apply Z.leb_le in Hx
  | Hx : (_ <? _) = true |- _ => apply Z.ltb_lt in Hx
  end.
  unfold nlk_wf. repeat match goal with |- _ /\ _ => split end; try lia.
  - intros i Hi.
    match goal with Hx : forallb _ (seq 0 (Z.to_nat (nk_n_chunks bs))) = true |- _ =>
      pose proof (forallb_nat _ _ Hx (Z.to_nat i) ltac:(lia)) as Hb end.
    cbv beta zeta in Hb. rewrite Z2Nat.id in Hb by lia.
    apply andb_true_iff in Hb as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
  - intros i Hi.
    match goal with Hx : forallb _ (seq 0 (Z.to_nat (nk_n_sent bs))) = true |- _ =>
      pose proof (forallb_nat _ _ Hx (Z.to_nat i) ltac:(lia)) as Hb end.
    cbv beta zeta in Hb. rewrite Z2Nat.id in Hb by lia.
    apply andb_true_iff in Hb as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.

Definition nlw_wfb (bs : list byte) : bool :=
  (0 <=? nw_n bs) && (nw_n bs <=? NL_CHUNK_MAX) && (0 <=? nw_full bs) && (nw_full bs <=? 1).
Lemma nlw_wfb_ok : forall bs, nlw_wfb bs = true -> nlw_wf bs.
Proof.
  intros bs H. unfold nlw_wfb in H. repeat rewrite andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. unfold nlw_wf. lia.
Qed.

(* ==========================================================================
   1. g_nl: 271992 bytes given by a byte function, first in the region list
   ========================================================================== *)

Fixpoint zbuild (g : Z -> byte) (o : Z) (k : nat) : list byte :=
  match k with O => [] | S k' => g o :: zbuild g (o + 1) k' end.
Lemma zbuild_length : forall g k o, length (zbuild g o k) = k.
Proof. intros g k. induction k as [|k IH]; intros o; cbn [zbuild length]; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma zbuild_nth : forall g k o i, (i < k)%nat -> nth_error (zbuild g o k) i = Some (g (o + Z.of_nat i)).
Proof.
  intros g k. induction k as [|k IH]; intros o i Hi; [lia|].
  destruct i as [|i]; cbn [zbuild nth_error].
  - replace (o + Z.of_nat 0) with o by lia. reflexivity.
  - rewrite IH by lia. replace (o + 1 + Z.of_nat i) with (o + Z.of_nat (S i)) by lia. reflexivity.
Qed.

Definition gbs (g : Z -> byte) : list byte := zbuild g 0 (Z.to_nat NK_SIZE).
Definition greg (g : Z -> byte) : wreg := (LA_G_NL, NK_SIZE, fun o => Some (g o)).

Lemma wlook_greg : forall g rest z, LA_G_NL <= z < LA_G_NL + NK_SIZE -> wlook (greg g :: rest) z = Some (g (z - LA_G_NL)).
Proof. intros g rest z Hz. cbn [wlook greg]. rewrite inrz_true by exact Hz. reflexivity. Qed.

Lemma gnl_bounds : 0 <= LA_G_NL /\ LA_G_NL + NK_SIZE < 2 ^ 64 /\ 0 < NK_SIZE.
Proof. unfold LA_G_NL, NK_SIZE. lia. Qed.

(* the length and the bytes of `gbs g`, with no tactic but rewrite near the list *)
Lemma gbs_len : forall g, Z.of_nat (length (gbs g)) = NK_SIZE.
Proof. intros g. unfold gbs. rewrite zbuild_length. apply Z2Nat.id. unfold NK_SIZE. lia. Qed.
Lemma gbs_nth : forall g i, (i < length (gbs g))%nat -> nth_error (gbs g) i = Some (g (Z.of_nat i)).
Proof.
  intros g i Hi. unfold gbs in *. rewrite zbuild_length in Hi.
  rewrite (zbuild_nth g _ 0 i Hi). rewrite Z.add_0_l. reflexivity.
Qed.

(* anlk_at over an abstract list holding g's bytes: lia never sees the 271992-byte list *)
Lemma anlk_of : forall segs g rest bs, Z.of_nat (length bs) = NK_SIZE ->
  (forall i, (i < length bs)%nat -> nth_error bs i = Some (g (Z.of_nat i))) ->
  anlk_at segs (wmem (greg g :: rest)) LA_G_NL bs.
Proof.
  intros segs g rest bs HLz HB. pose proof gnl_bounds as (G1 & G2 & G3).
  split; [|exact HLz]. split.
  - split; [lia|]. split; [lia|].
    intros i Hi. rewrite (HB i Hi). apply wmem_mbyte; [lia|].
    rewrite wlook_greg by lia. replace (LA_G_NL + Z.of_nat i - LA_G_NL) with (Z.of_nat i) by lia. reflexivity.
  - intros i Hi. rewrite HLz in Hi.
    apply (wmem_writable segs _ (LA_G_NL + i) (g i)); [lia|].
    rewrite wlook_greg by lia. replace (LA_G_NL + i - LA_G_NL) with i by lia. reflexivity.
Qed.
Lemma gbs_anlk : forall segs g rest, anlk_at segs (wmem (greg g :: rest)) LA_G_NL (gbs g).
Proof. intros segs g rest. apply anlk_of; [apply gbs_len | apply gbs_nth]. Qed.

(* the bytes of a g_nl state: a list of fields (offset, size, bytes) sorted by offset and disjoint (`fsorted`), 0
   elsewhere; the lookup stops at the first field past the offset, so a byte in a gap costs one or two compares *)
Definition gfield : Type := (Z * Z * list byte)%type.
Fixpoint flook (fs : list gfield) (o : Z) : byte :=
  match fs with
  | [] => zb 0
  | (off, n, l) :: t =>
      if o <? off then zb 0 else if o <? off + n then nth (Z.to_nat (o - off)) l (zb 0) else flook t o
  end.
Definition fsorted (fs : list gfield) : bool :=
  la_sorted (map (fun f => (fst (fst f), snd (fst f))) fs) &&
  forallb (fun f => Z.of_nat (length (snd f)) =? snd (fst f)) fs.
Definition fw (off : Z) (n : nat) (v : Z) : gfield := (off, Z.of_nat n, wle_bytes n v).

(* ==========================================================================
   2. The run's data
   ========================================================================== *)

(* errno (musl's static TLS, TFIB_ERRNO = TFIB_TP - 164) *)
Definition W_ERRNO : Z := 0x631b6c.
Definition W_TP : Z := 0x631c10.
(* the real-stack sp values *)
Definition KW_SP : Z := 0x7ffffffdd160.          (* LLVMFuzzerTestOneInput's s1, sp at its calls *)
Definition RA_SP : Z := KW_SP - 0x80.            (* reac_link_alias_read's realigned sp *)
Definition NT_SP : Z := RA_SP - 0xc0.            (* nl_talk's realigned sp *)
Definition KN_SP : Z := KW_SP - 0x160.           (* kernel's realigned sp (its s1) *)
(* the side stack *)
Definition W_LYF : Z := 0x7f0000000000.
Definition W_FRAME (cid : Z) : Z := W_LYF + fs_frame_off cid 0.
Definition FD_REQ : Z := W_FRAME 1 + 0x20.       (* reac_link_alias_read's request *)
Definition FR_BUF : Z := W_FRAME 9 + 0x20.       (* nl_talk's receive buffer *)
Definition FR_LEN : Z := 0x4000.
Definition AT_W : Z := W_FRAME 8 + 0x1130.       (* kernel's w2 *)
Definition NE_W : Z := AT_W.
Definition AT_S : Z := LA_STR_X.
Definition AT_SP : Z := KN_SP.
Definition NE_SP : Z := KN_SP.
(* the cursor in LLVMFuzzerTestOneInput's real frame, the input block *)
Definition KW_CUR : Z := KW_SP + 0x118.
Definition KW_IN : Z := 0x602000000050.
Definition KW_INB : list byte := map zb [0; 0; 16; 16; 0; 0; 0; 1; 0; 1; 0; 1; 4].

(* interfaces(): the table of 64 *)
Definition nlname (k : Z) : list byte :=
  map zb ([110; 108] ++ (if k <? 10 then [48 + k] else [48 + k / 10; 48 + k mod 10])).
Definition gname_byte (o : Z) : byte := nth (Z.to_nat (o mod 8)) (nlname (o / 8)) (zb 0).
Definition ODD_P : list Z := [0x20fe0; 0x21000; 0x21020; 0x21040].
Definition ODD_S : list (list byte) := map (map zb)
  [[101; 110; 112; 49; 51; 49; 115; 48; 46; 51; 51];   (* enp131s0.33 *)
   [101; 116; 104; 48];                                 (* eth0 *)
   [119; 108; 97; 110; 48];                             (* wlan0 *)
   [118; 101; 116; 104; 45; 98; 111; 120]].             (* veth-box *)
Definition tk (j : nat) : Z := Z.of_nat j + Z.of_nat j / 15.
Definition tptr (j : nat) : Z := if (j <? 60)%nat then LA_G_NAMES + 8 * tk j else nth (j - 60) ODD_P 0.
Definition tidx (j : nat) : Z := if (j <? 60)%nat then tk j + 2 else 101 + Z.of_nat (j - 60).
Definition tname (j : nat) : list byte := if (j <? 60)%nat then nlname (tk j) else nth (j - 60) ODD_S [].
Definition TAB : list (list byte * Z) := map (fun j => (tname j, tidx j)) (seq 0 64).
Definition TBLP : list byte := flat_map (fun j => wle_bytes 8 (tptr j)) (seq 0 64).
Definition TBLI : list byte := flat_map (fun j => wle_bytes 4 (tidx j)) (seq 0 64).

(* the texts table and its strings *)
Definition TXT_P : list Z :=
  [0x20fc0; 0x21100; 0x21120; 0x21140; 0x21160; 0x21180; 0x211a0; 0x211c0; 0x211e0; 0x21200; 0x21220].
Definition TXT_S : list (list byte) := map (map zb)
  [[];
   [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100];       (* reac-pw:served *)
   [114; 101; 97; 99; 45; 112; 119; 58; 109; 105; 110; 116; 101; 100];       (* reac-pw:minted *)
   [104; 111; 115; 116; 45; 97; 108; 105; 97; 115];                          (* host-alias *)
   [114; 101; 97; 99; 45; 112; 119; 58];                                     (* reac-pw: *)
   [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100; 50];   (* reac-pw:served2 *)
   [114; 101; 97; 99; 45; 112; 119];                                         (* reac-pw *)
   [118; 108; 97; 110];                                                      (* vlan *)
   [118; 101; 116; 104];                                                     (* veth *)
   [118; 108; 97; 110; 120];                                                 (* vlanx *)
   [118; 108; 97]].                                                          (* vla *)
(* the slack a word-wise strlen may read after the NUL of s at p *)
Definition kslack (p : Z) (s : list byte) : list byte :=
  repeat (zb 0) (Z.to_nat ((- (p + Z.of_nat (length s) + 1)) mod 8)).
Definition CODEB : list byte := flat_map (wle_bytes 4) [4294967295; 4294967277; 4294967201; 5].

(* the .rodata objects: each in its 32-byte slot (nl_errno.e: 64), the rest of the slot 0 *)
Definition slot32 (s : list byte) : list byte := s ++ repeat (zb 0) (32 - length s).
Fixpoint oflook (fs : list gfield) (z : Z) : option byte :=
  match fs with
  | [] => None
  | (a, n, l) :: t => if inrz z a n then nth_error l (Z.to_nat (z - a)) else oflook t z
  end.
Definition ROD_LO : Z := 0x20fc0.
Definition ROD_N : Z := 0x280.
Definition ROD : list gfield :=
  [(LA_STR_EMPTY, 32, slot32 []);
   (nth 0 ODD_P 0, 32, slot32 (nth 0 ODD_S [])); (nth 1 ODD_P 0, 32, slot32 (nth 1 ODD_S []));
   (nth 2 ODD_P 0, 32, slot32 (nth 2 ODD_S [])); (nth 3 ODD_P 0, 32, slot32 (nth 3 ODD_S []));
   (LA_NL_ERRNO_E, 64, flat_map (wle_bytes 4) nl_errno_tab ++ repeat (zb 0) 40);
   (LA_STR_X, 32, slot32 [zb 0x78]);
   (LA_MSG_CODES, 32, CODEB ++ repeat (zb 0) 16)] ++
  map (fun j => (nth j TXT_P 0, 32, slot32 (nth j TXT_S []))) (seq 1 10).

(* g_nl states *)
Definition G0 : list gfield := [(NK_IF_NAME, 512, TBLP); (NK_IF_INDEX, 256, TBLI); fw NK_N_IF 4 64].
Definition CH0 : list byte :=
  map zb ([0x28; 0; 0; 0; 0x10; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0] ++ repeat 0 16 ++ [6; 0; 3; 0; 0x78; 0; 0; 0]).
Definition REQB : list byte :=
  map zb [0x20; 0; 0; 0; 0x12; 0; 1; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition GK : list gfield :=
  [(NK_CHUNK, 40, CH0); fw NK_CHUNK_LEN 8 40; fw NK_N_CHUNKS 4 1; fw NK_END_ERRNO 4 E_NOBUFS].
Definition GO : list gfield := [fw NK_OPEN 4 1; fw NK_OPENED 4 1].
Definition G1 : list gfield := GK ++ G0.
Definition G2 : list gfield := GK ++ GO ++ G0.
Definition G3 : list gfield := GK ++ GO ++ [(NK_SENT, 32, REQB); fw NK_SENT_LEN 8 32; fw NK_N_SENT 4 1] ++ G0.
(* each state's fields are in offset order, disjoint, and each holds exactly its bytes *)
Lemma G_sorted : fsorted G0 && fsorted G1 && fsorted G2 && fsorted G3 = true.
Proof. vm_compute. reflexivity. Qed.

(* w2 at attr_text's call *)
Definition AT_WB : list byte := wput (wput (wput (repeat (zb 0) (Z.to_nat NW_SIZE)) 4 2 16) 8 4 1) NW_N 8 32.

(* regions *)
Definition zsh (a n : Z) : wreg := (shadow_addr a - 64, n / 8 + 128, fun _ => Some (zb 0)).
Definition zreg (a n : Z) : wreg := (a, n, fun _ => Some (zb 0)).
Definition lreg (a : Z) (l : list byte) (n : Z) : wreg := (a, n, fun o => nth_error l (Z.to_nat o)).
Definition R_GN : wreg := (LA_G_NAMES, 512, fun o => Some (gname_byte o)).
Definition R_ROD : wreg := (ROD_LO, ROD_N, fun o => oflook ROD (ROD_LO + o)).
Definition R_TXT : wreg := lreg LA_TEXTS (flat_map (wle_bytes 8) TXT_P) 88.

(* ==========================================================================
   3. The tactics
   ========================================================================== *)

(* the interface table of g_nl, entry by entry *)
Lemma nth_map_seq : forall (A : Type) (f : nat -> A) n i x, nth_error (map f (seq 0 n)) i = Some x -> (i < n)%nat /\ x = f i.
Proof.
  intros A f n i x H. rewrite nth_error_map in H.
  destruct (Nat.lt_ge_cases i n) as [Hi|Hi].
  - rewrite nth_error_seq0 in H by exact Hi. cbn [option_map] in H. injection H as H. subst x. split; [exact Hi | reflexivity].
  - assert (E : nth_error (seq 0 n) i = None) by (apply nth_error_None; rewrite length_seq; exact Hi).
    rewrite E in H. discriminate.
Qed.

Definition ent_ok (rs : list wreg) (j : nat) : bool :=
  (0 <=? tidx j) && (tidx j <? 2 ^ 31) &&
  wc_val rs (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) 8 (tptr j) && negb (tptr j =? 0) &&
  wc_cstr rs (tptr j) (tname j) &&
  wc_val rs (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat j) 4 (tidx j).

Lemma tab_sound : forall segs rs bs, nk_n_if bs = 64 -> forallb (ent_ok rs) (seq 0 64) = true ->
  aiftab_at segs (wmem rs) LA_G_NL bs TAB.
Proof.
  intros segs rs bs Hn Hf. split; [rewrite Hn; reflexivity|]. split; [apply Z.leb_le; reflexivity|].
  intros i nm ix H. unfold TAB in H. apply nth_map_seq in H as [Hi E]. cbv beta in E. injection E as E1 E2. subst nm ix.
  pose proof (forallb_nat _ _ Hf i Hi) as Hb. unfold ent_ok in Hb. repeat rewrite andb_true_iff in Hb.
  destruct Hb as [[[[[H1 H2] H3] H4] H5] H6].
  split; [split; [apply Z.leb_le; exact H1 | apply Z.ltb_lt; exact H2]|].
  exists (tptr i). split; [exact (wc_val_ok segs _ _ _ _ H3)|].
  split; [apply negb_true_iff in H4; apply Z.eqb_neq; exact H4|].
  split; [exact (wc_cstr_ok segs _ _ _ H5) | exact (wc_val_ok segs _ _ _ _ H6)].
Qed.

(* the 8 bytes of a word fix it modulo 2 ^ 64 *)
Lemma le8_inj : forall x y, (forall k, (k < 8)%nat -> YO0f.le_byte x 8 k = YO0f.le_byte y 8 k) ->
  x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
  intros x y H. apply Z.bits_inj'. intros n Hn.
  destruct (Z.lt_ge_cases n 64) as [Hlt|Hge].
  - pose proof (Z.div_mod n 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm.
    set (q := n / 8) in *. set (r := n mod 8) in *.
    assert (Hk : (Z.to_nat q < 8)%nat) by lia.
    pose proof (H _ Hk) as E. unfold YO0f.le_byte in E. rewrite Z2Nat.id in E by lia.
    change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
    assert (G : forall z, Z.testbit (z mod 2 ^ 64) n = Z.testbit (Z.shiftr (z mod 2 ^ 64) (8 * q) mod 256) r).
    { intros z. change 256 with (2 ^ 8).
      rewrite (Z.mod_pow2_bits_low (Z.shiftr (z mod 2 ^ 64) (8 * q)) 8 r) by lia.
      rewrite (Z.shiftr_spec (z mod 2 ^ 64) (8 * q) r) by lia. f_equal; lia. }
    rewrite (G x), (G y), E. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma val8_mod : forall segs m a x y, val_mem segs m a 8 x -> val_mem segs m a 8 y -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
  intros segs m a x y Hx Hy. apply le8_inj. intros k Hk.
  pose proof (Hx k Hk) as E. rewrite (Hy k Hk) in E.
  apply (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end)) in E. cbv beta iota in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E.
  change (2 ^ Z.of_N 8) with 256 in E.
  unfold YO0f.le_byte, YG0f.le_byte in *. rewrite !Z.mod_mod in E by lia.
  symmetry. exact E.
Qed.

(* two C strings at one address: the shorter is a prefix, so no longer than the other *)
Lemma cstr_len_le : forall segs m p s1 s2, acstr_at segs m p s1 -> acstr_at segs m p s2 -> (length s1 <= length s2)%nat.
Proof.
  intros segs m p s1 s2 [[_ [_ H1]] N1] [[_ [_ H2]] _].
  destruct (Nat.le_gt_cases (length s1) (length s2)) as [Hle|Hgt]; [exact Hle|]. exfalso.
  pose proof (H2 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as E2.
  pose proof (H1 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as E1.
  rewrite nth_error_app2 in E2 by lia. rewrite Nat.sub_diag in E2. change (nth_error [zb 0] 0) with (Some (zb 0)) in E2.
  rewrite nth_error_app1 in E1 by lia. rewrite E2 in E1.
  apply N1. apply (nth_error_In s1 (length s2)). rewrite <- E1. reflexivity.
Qed.

(* the strcmp wrapper's facts of one string (fuzz_if_nametoindex_c.v astrcmp_arg_ni) *)
Definition scmp_ok (rs : list wreg) (sp K p : Z) (s : list byte) : bool :=
  let n := Z.of_nat (length s) + 1 in
  (0 <? p) && (n <? 2 ^ 32) && amrb p n && wc_ra rs p n && wc_hull rs p n && apartb p n (sp - K) K
  && wc_tail rs (p + Z.of_nat (length s)).
Lemma scmp_ok_sound : forall segs rs regs sp K p s, spZ regs = sp -> scmp_ok rs sp K p s = true ->
  astrcmp_arg_ni segs regs K (wmem rs) p s.
Proof.
  intros segs rs regs sp K p s Hsp H. cbv beta zeta delta [scmp_ok] in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[H1 H2] H3] H4] H5] H6] H7].
  unfold astrcmp_arg_ni. split; [apply Z.ltb_lt; exact H1|]. split; [apply Z.ltb_lt; exact H2|].
  split; [exact (amrb_ok _ _ H3)|]. split; [exact (wc_ra_ok segs _ _ _ H4)|]. split; [exact (wc_hull_ok segs _ _ _ H5)|].
  split; [exact (apart_frame_of regs sp K p _ Hsp H6)|].
  exact (wc_tail_ok segs rs _ H7).
Qed.

Definition tsc_ok (rs : list wreg) (sp K : Z) (j : nat) : bool :=
  ent_ok rs j && scmp_ok rs sp K (tptr j) (tname j) && (0 <=? tptr j) && (tptr j <? 2 ^ 64).
Lemma tab_scmp : forall segs rs regs sp K, spZ regs = sp -> forallb (tsc_ok rs sp K) (seq 0 64) = true ->
  forall i n2 ix p, nth_error TAB i = Some (n2, ix) ->
    au64_at segs (wmem rs) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
    astrcmp_arg_ni segs regs K (wmem rs) p n2.
Proof.
  intros segs rs regs sp K Hsp Hf i n2 ix p Hn Hp Hr.
  unfold TAB in Hn. apply nth_map_seq in Hn as [Hi E]. cbv beta in E. injection E as E1 E2. subst n2.
  pose proof (forallb_nat _ _ Hf i Hi) as Hb. unfold tsc_ok in Hb. repeat rewrite andb_true_iff in Hb.
  destruct Hb as [[[He Hs] H0] H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  unfold ent_ok in He. repeat rewrite andb_true_iff in He. destruct He as [[[[[_ _] Hv] _] _] _].
  pose proof (val8_mod segs _ _ _ _ Hp (wc_val_ok segs _ _ _ _ Hv)) as M.
  rewrite (Z.mod_small p) in M by lia. rewrite (Z.mod_small (tptr i)) in M by lia. subst p.
  exact (scmp_ok_sound segs rs regs sp K _ _ Hsp Hs).
Qed.

(* kernel's separation (kernel_c.v kernel_apart), as a boolean, and modulo 2 ^ 64 *)
Definition kab (a n : Z) : bool :=
  apartb a n (KW_SP - KERNEL_AK) KERNEL_AK && apartb a n LA_G_NL NK_SIZE &&
  apartb a n LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3) && apartb a n KW_CUR 16.
Lemma kab_ok : forall regs a n, spZ regs = KW_SP -> aarg regs 0 = KW_CUR -> kab a n = true -> kernel_apart regs a n.
Proof.
  intros regs a n Hsp Ha H. unfold kab in H. repeat rewrite andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  apply apartb_ok in H1. apply apartb_ok in H2. apply apartb_ok in H3. apply apartb_ok in H4.
  unfold kernel_apart, apart_frame, apart_gnl. rewrite Hsp, Ha. unfold apart in *.
  split; [lia|]. split; [lia|]. split; lia.
Qed.
Lemma kab_shift : forall regs t n n' k, spZ regs = KW_SP -> aarg regs 0 = KW_CUR -> kab t n = true ->
  0 <= t -> t + n <= 2 ^ 64 -> 0 <= n' <= n -> kernel_apart regs (t + 2 ^ 64 * k) n'.
Proof.
  intros regs t n n' k Hsp Ha H Ht Htn Hn. unfold kab in H. repeat rewrite andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply apartb_ok in H1. apply apartb_ok in H2. apply apartb_ok in H3. apply apartb_ok in H4.
  unfold kernel_apart, apart_frame, apart_gnl. rewrite Hsp, Ha. unfold apart in *.
  rewrite KERNEL_AK_val in *. unfold KW_CUR, KW_SP, LA_G_NL, NK_SIZE, LA_LONG_ALIAS, LONG_ALIAS_SIZE in *.
  destruct (Z.lt_trichotomy k 0) as [Hk|[Hk|Hk]].
  - assert (2 ^ 64 * k <= - 2 ^ 64) by lia. split; [lia|]. split; [lia|]. split; lia.
  - subst k. rewrite Z.mul_0_r, Z.add_0_r. split; [lia|]. split; [lia|]. split; lia.
  - assert (2 ^ 64 <= 2 ^ 64 * k) by lia. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* kernel's clause on the interface names: any table the Pre's view allows names the strings of the memory *)
Definition kent_ok (rs : list wreg) (j : nat) : bool :=
  wc_val rs (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat j) 8 (tptr j) && wc_cstr rs (tptr j) (tname j) &&
  (0 <=? tptr j) && (tptr j + (Z.of_nat (length (tname j)) + 1) <=? 2 ^ 64) &&
  kab (tptr j) (Z.of_nat (length (tname j)) + 1).
Lemma kernel_names : forall segs rs regs bs, spZ regs = KW_SP -> aarg regs 0 = KW_CUR ->
  nk_n_if bs = 64 -> forallb (kent_ok rs) (seq 0 64) = true ->
  forall tab i nm ix p, aiftab_at segs (wmem rs) LA_G_NL bs tab -> nth_error tab i = Some (nm, ix) ->
    au64_at segs (wmem rs) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
    kernel_apart regs p (Z.of_nat (length nm) + 1).
Proof.
  intros segs rs regs bs Hsp Ha Hn Hf tab i nm ix p Htab Hnth Hp.
  destruct Htab as (Hn' & _ & Hent).
  assert (Hi : (i < 64)%nat).
  { assert (Hl : length tab = 64%nat) by lia.
    rewrite <- Hl. apply nth_error_Some. rewrite Hnth. discriminate. }
  destruct (Hent i nm ix Hnth) as (_ & p' & Hp' & _ & Hc & _).
  pose proof (forallb_nat _ _ Hf i Hi) as Hb. unfold kent_ok in Hb. repeat rewrite andb_true_iff in Hb.
  destruct Hb as [[[[H1 H2] H3] H4] H5].
  pose proof (wc_val_ok segs _ _ _ _ H1) as Hv. pose proof (wc_cstr_ok segs _ _ _ H2) as Hs.
  apply Z.leb_le in H3. apply Z.leb_le in H4.
  assert (Hr' : 0 <= p' < 2 ^ 64).
  { pose proof Hc as [[Hc1 [Hc2 _]] _]. rewrite length_app in Hc2. cbn [length] in Hc2. lia. }
  assert (E' : p' = tptr i).
  { pose proof (val8_mod segs _ _ _ _ Hp' Hv) as M.
    rewrite (Z.mod_small p') in M by lia. rewrite (Z.mod_small (tptr i)) in M by lia. exact M. }
  subst p'.
  pose proof (cstr_len_le segs _ _ _ _ Hc Hs) as Hle.
  pose proof (val8_mod segs _ _ _ _ Hp Hv) as M. rewrite (Z.mod_small (tptr i)) in M by lia.
  assert (Ek : exists k, p = tptr i + 2 ^ 64 * k).
  { exists (p / 2 ^ 64). pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as Hd. lia. }
  destruct Ek as [k ->].
  apply (kab_shift regs (tptr i) (Z.of_nat (length (tname i)) + 1) _ k Hsp Ha H5); lia.
Qed.

Ltac wck := vm_compute; reflexivity.
Ltac wgoal :=
  lazymatch goal with
  | |- anlk_at _ (wmem _) _ _ => apply gbs_anlk
  | |- nlk_wf _ => apply nlk_wfb_ok; wck
  | |- nlw_wf _ => apply nlw_wfb_ok; wck
  | |- anlw_at _ (wmem _) _ _ => split; [apply wc_u8_ok; wck | wck]
  | |- au8arr _ (wmem _) _ _ => apply wc_u8_ok; wck
  | |- abuf _ (wmem _) _ ?n => exists (repeat (zb 0) (Z.to_nat n)); split; [wck | apply wc_u8_ok; wck]
  | |- abytes _ (wmem _) _ _ => apply wc_bytes_ok; wck
  | |- awrange _ (wmem _) _ _ => apply wc_wr_ok; wck
  | |- range_addressable (ard _ (wmem _)) _ _ _ => apply wc_ra_ok; wck
  | |- shadow_hull_vis (ard _ (wmem _)) _ _ => apply wc_hull_ok; wck
  | |- au32_at _ (wmem _) _ _ => apply wc_val_ok; wck
  | |- au64_at _ (wmem _) _ _ => apply wc_val_ok; wck
  | |- acstr_at _ (wmem _) _ _ => apply wc_cstr_ok; wck
  | |- aiftab_at _ (wmem _) _ _ _ => apply tab_sound; wck
  | |- astrcmp_arg_ni _ _ _ (wmem _) _ _ => eapply scmp_ok_sound; [eassumption | wck]
  | |- kernel_apart _ _ _ => eapply kab_ok; [eassumption | eassumption | wck]
  | |- amem_range _ _ => apply amrb_ok; wck
  | |- apart_frame _ _ _ _ => eapply apart_frame_of; [eassumption | wck]
  | |- apart_gnl _ _ _ => apply apgb_ok; wck
  | |- apart _ _ _ _ => apply apartb_ok; wck
  | |- _ \/ _ => first [left; wgoal | right; wgoal]
  | |- _ <> 0 => apply Z.eqb_neq; wck
  | |- _ <= _ => apply Z.leb_le; wck
  | |- _ < _ => apply Z.ltb_lt; wck
  | |- _ = _ => wck
  | |- _ -> _ => intros _; wgoal
  end.
Ltac wsplit := repeat match goal with |- _ /\ _ => split end.
Ltac wall := wsplit; wgoal.

(* ==========================================================================
   4. fuzz_socket, fuzz_send, fuzz_recv (nl_talk's exchange)
   ========================================================================== *)

Definition FS_RS : list wreg := [greg (flook G1); zreg W_ERRNO 4; zsh W_ERRNO 4].
Definition fs_mem : word -> option byte := wmem FS_RS.

(* the Pre lambda of fuzz_socket_acontract holds at fs_mem, for every segment list and every image instance whose
   errno and tp are image A's, at every register file with nl_talk's sp *)
Lemma fuzz_socket_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = W_ERRNO -> as_tp B = W_TP -> spZ regs = NT_SP -> fuzz_socket_apre segs B regs fs_mem.
Proof.
  intros segs B regs HE HT Hsp. unfold fuzz_socket_apre, fs_mem. rewrite HE, HT.
  exists (gbs (flook G1)). wall.
Qed.

Definition FD_RS : list wreg :=
  [greg (flook G2); zreg W_ERRNO 4; lreg FD_REQ REQB 32; zsh LA_G_NL NK_SIZE; zsh W_ERRNO 4; zsh FD_REQ 32].
Definition fd_mem : word -> option byte := wmem FD_RS.

(* ... at fd_mem, with a1 = the request, a2 = 32 and nl_talk's sp *)
Lemma fuzz_send_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = W_ERRNO -> as_tp B = W_TP -> aarg regs 1 = FD_REQ -> aarg regs 2 = 32 -> spZ regs = NT_SP ->
  fuzz_send_apre segs B regs fd_mem.
Proof.
  intros segs B regs HE HT H1 H2 Hsp. unfold fuzz_send_apre, fd_mem. rewrite HE, HT, H1, H2.
  exists (gbs (flook G2)), REQB. wall.
Qed.

Definition FR_RS : list wreg :=
  [greg (flook G3); zreg W_ERRNO 4; zreg FR_BUF FR_LEN; zsh LA_G_NL NK_SIZE; zsh W_ERRNO 4; zsh FR_BUF FR_LEN].
Definition fr_mem : word -> option byte := wmem FR_RS.

(* ... at fr_mem, with a1 = nl_talk's receive buffer, a2 = 0x4000 and nl_talk's sp *)
Lemma fuzz_recv_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = W_ERRNO -> as_tp B = W_TP -> aarg regs 1 = FR_BUF -> aarg regs 2 = FR_LEN -> spZ regs = NT_SP ->
  fuzz_recv_apre segs B regs fr_mem.
Proof.
  intros segs B regs HE HT H1 H2 Hsp. unfold fuzz_recv_apre, fr_mem. rewrite HE, HT, H1, H2.
  exists (gbs (flook G3)). wall.
Qed.

(* ==========================================================================
   5. fuzz_if_nametoindex (reac_link_alias_read on "nl0")
   ========================================================================== *)

Definition FI_RS : list wreg :=
  [greg (flook G1); R_GN; R_ROD; zsh LA_G_NL NK_SIZE; zsh LA_G_NAMES 512; zsh ROD_LO ROD_N].
Definition fi_mem : word -> option byte := wmem FI_RS.

(* ... at fi_mem, with a0 = g_names[0] and reac_link_alias_read's sp; the table is interfaces()' 64 entries *)
Lemma fuzz_if_nametoindex_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = LA_G_NAMES -> spZ regs = RA_SP -> fuzz_if_nametoindex_apre segs regs fi_mem.
Proof.
  intros segs regs H0 Hsp. unfold fuzz_if_nametoindex_apre, fi_mem. rewrite H0.
  exists (gbs (flook G1)), TAB, (nlname 0). wsplit; try wgoal.
  eapply tab_scmp; [eassumption | wck].
Qed.

(* ==========================================================================
   6. kernel (LLVMFuzzerTestOneInput's op_read, at 0x82ec0)
   ========================================================================== *)

Definition KW_RS : list wreg :=
  [greg (flook G0); R_GN; zreg LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3); R_ROD; R_TXT;
   lreg KW_CUR (wle_bytes 8 (KW_IN + 4) ++ wle_bytes 8 9) 16; lreg KW_IN KW_INB 13;
   zsh LA_G_NL NK_SIZE; zsh LA_G_NAMES 512; zsh LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3); zsh ROD_LO ROD_N;
   zsh LA_TEXTS 88; zsh KW_CUR 16; zsh KW_IN 13].
Definition kw_mem : word -> option byte := wmem KW_RS.

Ltac kw_cur := exists (KW_IN + 4), 9; wsplit; try wgoal; exists (skipn 4 KW_INB); split; wgoal.
Ltac kw_err :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as Hc by lia;
  clear Hi; destruct Hc as [->|[->|[->|[->|[->| ->]]]]]; wgoal.
Ltac kw_codes := exists CODEB; split; wgoal.
Ltac kw_txt :=
  let i := fresh "i" in let Hi := fresh "Hi" in
  intros i Hi; unfold TEXTS_N in Hi;
  exists (nth (Z.to_nat i) TXT_P 0); split;
  [ | unfold kernel_str; exists (nth (Z.to_nat i) TXT_S []), (kslack (nth (Z.to_nat i) TXT_P 0) (nth (Z.to_nat i) TXT_S [])) ];
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) as Hc by lia;
  clear Hi; destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; wall.
Ltac kw_kstr :=
  unfold kernel_str;
  first [ exists (@nil byte), (kslack LA_STR_EMPTY []); wall
        | exists [zb 0x78], (kslack LA_STR_X [zb 0x78]); wall ].
Ltac kw_long := exists (repeat (zb 0) 300), (repeat (zb 0) 3); wall.
Ltac kw_names := eapply kernel_names; [eassumption | eassumption | wck | wck].

(* ... at kw_mem, with a0 = the cursor and LLVMFuzzerTestOneInput's sp *)
Lemma kernel_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = KW_CUR -> spZ regs = KW_SP -> kernel_apre segs regs kw_mem.
Proof.
  intros segs regs H0 Hsp. unfold kernel_apre, kw_mem. rewrite H0.
  exists (gbs (flook G0)). wsplit; try wgoal.
  all: first [ solve [kw_cur] | solve [kw_err] | solve [kw_codes] | solve [kw_txt] | solve [kw_kstr]
             | solve [kw_long] | solve [kw_names] ].
Qed.

(* ==========================================================================
   7. attr_text and nl_error (kernel's w2)
   ========================================================================== *)

Definition AT_RS : list wreg := [lreg AT_W AT_WB NW_SIZE; R_ROD; zsh AT_W NW_SIZE; zsh ROD_LO ROD_N].
Definition at_mem : word -> option byte := wmem AT_RS.

(* ... at at_mem, with a0 = w2, a2 = "x" and kernel's sp *)
Lemma attr_text_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = AT_W -> aarg regs 2 = AT_S -> spZ regs = AT_SP -> attr_text_apre segs regs at_mem.
Proof.
  intros segs regs H0 H2 Hsp. unfold attr_text_apre, at_mem. rewrite H0, H2.
  exists AT_WB, [zb 0x78]. wsplit; try wgoal.
  all: exists (kslack AT_S [zb 0x78]); split; wgoal.
Qed.

Definition NE_RS : list wreg := [zreg NE_W NW_SIZE; zsh NE_W NW_SIZE].
Definition ne_mem : word -> option byte := wmem NE_RS.

(* ... at ne_mem, with a0 = w2, a2 = 2 ^ 64 - 1 (the cut -1) and kernel's sp *)
Lemma nl_error_apre_sat : forall segs (regs : bvmap 5 word),
  aarg regs 0 = NE_W -> aarg regs 2 = 2 ^ 64 - 1 -> spZ regs = NE_SP -> nl_error_apre segs regs ne_mem.
Proof.
  intros segs regs H0 H2 Hsp. unfold nl_error_apre, ne_mem. rewrite H0, H2.
  exists (repeat (zb 0) (Z.to_nat NW_SIZE)). wall.
Qed.

(* the value the imports left *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
