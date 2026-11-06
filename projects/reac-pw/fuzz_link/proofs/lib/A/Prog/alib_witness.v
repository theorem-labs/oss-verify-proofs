(* Satisfiability witnesses of the function-specific Pre of the three library contracts (nl_talk_c.v,
   reac_link_alias_read_c.v, reac_link_alias_write_c.v), at ONE memory `w_mem` holding the values a real run holds at the
   three calls. The journal part of each Pre (link_amem.v `apre`) needs AR of image A's start state, which the start-up
   files give; it is written out in link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) and in nl_talk_c.v's
   header. Each lemma holds for every segment list: `w_mem` holds every byte the Pre reads, so no ROM byte is read.

   THE RUN (link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1; fuzz_link.c:764-790 and :677-700).
   LLVMFuzzerTestOneInput memsets g_nl, calls interfaces() and kernel(); op_read calls text_buf twice and
   reac_link_alias_read(name, kind, 16, alias, 16), which builds the 32-byte RTM_GETLINK in its class-1 side frame and
   calls nl_talk(req, 32, kind, 16, alias, 16). The memory below is that state, before the socket opens.
   - g_nl at LA_G_NL = 0x5dcac0, NK_SIZE = 271992 bytes: open = opened = closed = misuse = 0, socket_errno =
     send_errno = 0 (kernel()'s flags & 3 = 0, fuzz_link.c:262-263), end_errno = 105 = E_NOBUFS (kernel() takes it
     from nl_errno, whose table holds no 0: netlink.h:159, link_spec.v nl_errno_tab), n_sent = 0, n_chunks = 1 with
     chunk_len[0] = 36 and chunk[0] the NLMSG_ERROR that an ACK is (nl_error(w, 0, -1), netlink.h:307-315: a
     16-byte header of length 36, type 2, flags 0, seq 1, pid 0, then 20 zero body bytes), next = 0, n_if = 64.
   - the interface table interfaces() builds (fuzz_link.c:86-100): for k = 0..62 with k mod 16 <> 15 (15, 31 and 47
     are skipped, 60 entries) entry j holds g_names[k] = "nl<k>" at LA_G_NAMES + 8 k with if_index k + 2, where
     k = j + j / 15; entries 60..63 hold odd[1..4] = "enp131s0.33", "eth0", "wlan0", "veth-box" at the .rodata
     addresses 0x20fe0, 0x21000, 0x21020, 0x21040 with if_index 101..104. Those four addresses are the pointers of
     the .data.rel.ro table LA_ODD = 0xa1760, entries 1..4, and the strings are the bytes at them; both were read
     as DATA from the pinned image fuzz_link.asan (sha256 059dae63e07c) with pyelftools 0.33, 2026-10-30.
     Entry 2 is "nl2" with if_index 4, so the request a read of "nl2" sends is link_spec's `req_read 4`
     (`req_z_is` below).
   - errno = 0 at TFIB_ERRNO 0x631b6c = TFIB_TP 0x631c10 - 164 (lib/A/AF0m.v).
   - the request: 32 bytes at W_REQ = 0x7f0000002020, reac_link_alias_read's class-1 side frame + 32 (fake stack,
     below alloc_ceiling, high memory), holding `req_read 4`.
   - op_read's two text_buf(16) blocks (malloc(17), 17 bytes 0x5a, fuzz_link.c:655-665) at W_KB = 0x602000000010
     and W_AB = 0x602000000030; for reac_link_alias_write the alias is the .rodata string texts[7] = "vlan" at
     W_AL = 0x211c0 (the pointers of the .data.rel.ro table LA_TEXTS = 0xa17c0 and the bytes at them were read as
     DATA from the pinned image, as above; text_of returns a texts entry whenever the input's selector byte has
     bit 7 clear, fuzz_link.c:120-136), with its NUL at 0x211c4 and the three bytes 0x211c5..0x211c7, all 0,
     which is strlen's slack to the next 8-boundary.
   - the stack pointers: SP_NT = 0x7ffffffde000 (nl_talk's entry sp, which is reac_link_alias_read's realigned
     sp), SP_AR = SP_AW = SP_NT + 0x100 (the two readers' entry sp). Each lemma stands alone: the three values are
     not one chain ((SP_AR - 128) rounded down to 32 is 0x7ffffffde080, not SP_NT); each keeps every object outside
     its window [sp - K, sp).

   THE SHADOW. In `w_mem` every shadow byte the three Pres read is 0, over three bands with margin, as form_witness.v's
   `ca_mem` does: [0x7fff7000, 0x800c9000) is the shadow of [0, 0x640000), which holds g_nl, g_names, the four
   .rodata strings and errno; [0xc047fff7000, 0xc047fff9000) the shadow of the two heap blocks;
   [0xfe07fff8000, 0xfe07fff9000) the shadow of the request's frame bytes. On image A the first band is 0 over
   g_nl's, g_names' and errno's bytes by AR's zero shadow of the image (lib/A/AF0m.v Tfib_zero_shadow), and in the
   last granule of each odd string and of "vlan" (instrumented .rodata globals) it is the string's size mod 8
   (0x04, 0x05, 0x06, 0x01 at shadow(0x20fe8), shadow(0x21000), shadow(0x21020), shadow(0x21048); 0x05 at
   shadow(0x211c0): AF0m.v const cells), which `saddr_ok` accepts for every
   byte of the string and its NUL; a malloc(17) block's three granules are 0, 0, 1 with 0xfa redzones
   (shHeapLeftRz, Reusable/YG00.v:41, chunk_granule); the frame band is 0 after frame_alloc_1's `zero_shadow` and
   the unpoisoning at reac_link_alias_read +0x184..+0x190, but for the frame's redzones: 0xf1 at its shadow bytes
   0..3 and 0xf3 at its bytes 8..11 (+0xf0..+0x114). The Pres ask `range_addressable` only over object bytes,
   where every value the image holds passes `saddr_ok`, and `shadow_hull_vis` only that the hull's bytes are
   READABLE; so 0 everywhere is a memory that meets every conjunct.

   No tactic ever sees the 271992-byte list `gnl_bs` itself (form_witness.v's lesson): it is `map f (seq 0
   NK_SIZE)`, so `nth_error` is a rewrite, its length is `length_map` / `length_seq`, and each g_nl field is read
   by `gnl_f4` / `gnl_f8`, which turn `rdn` into four or eight applications of the byte FUNCTION. The 64 table
   entries are proved by ONE vm_compute'd boolean check (`ent_all`) over `seq 0 64` and one generic soundness
   lemma, never by 64 hand cases.

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YP09 YP03 YI04 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem form_witness nl_talk_c reac_link_alias_read_c reac_link_alias_write_c.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ==========================================================================
   0. Arithmetic and list lemmas
   ========================================================================== *)

Lemma E64 : (2:Z) ^ 64 = 18446744073709551616. Proof. reflexivity. Qed.
Lemma E32 : (2:Z) ^ 32 = 4294967296. Proof. reflexivity. Qed.
Lemma E31 : (2:Z) ^ 31 = 2147483648. Proof. reflexivity. Qed.

Ltac orbt := repeat (rewrite orb_true_l || rewrite orb_true_r); reflexivity.

Lemma some_inj : forall {A} (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. injection H as H. exact H. Qed.

Lemma zb_mod : forall x y, zb x = zb y -> x mod 256 = y mod 256.
Proof.
  intros x y H. unfold zb in H. apply (f_equal bv_unsigned) in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

(* the little-endian byte of a value, as a plain division *)
Definition wle (v k : Z) : Z := (v / 2 ^ (8 * k)) mod 256.

(* YI04's `le_byte` (the one its `val_mem` names) as a division *)
Lemma le_byte_div : forall v (n k : nat),
  le_byte v n k = ((v mod 2 ^ (8 * Z.of_nat n)) / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
  intros v n k. try unfold YG0f.le_byte. try unfold YO0f.le_byte.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma z64_bytes : forall v, 0 <= v < 2 ^ 64 ->
  (v / 2 ^ 0) mod 256 + 256 * ((v / 2 ^ 8) mod 256 + 256 * ((v / 2 ^ 16) mod 256
  + 256 * ((v / 2 ^ 24) mod 256 + 256 * ((v / 2 ^ 32) mod 256 + 256 * ((v / 2 ^ 40) mod 256
  + 256 * ((v / 2 ^ 48) mod 256 + 256 * ((v / 2 ^ 56) mod 256))))))) = v.
Proof.
  intros v Hv.
  replace (2 ^ 0) with 1 by reflexivity. rewrite Z.div_1_r.
  replace (2 ^ 8) with 256 by reflexivity.
  replace (2 ^ 16) with (256 * 256) by reflexivity.
  replace (2 ^ 24) with (256 * 256 * 256) by reflexivity.
  replace (2 ^ 32) with (256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ 40) with (256 * 256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ 48) with (256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
  replace (2 ^ 56) with (256 * 256 * 256 * 256 * 256 * 256 * 256) by reflexivity.
  rewrite <- !Z.div_div by lia.
  set (v1 := v / 256). set (v2 := v1 / 256). set (v3 := v2 / 256). set (v4 := v3 / 256).
  set (v5 := v4 / 256). set (v6 := v5 / 256). set (v7 := v6 / 256).
  assert (E7 : v7 mod 256 = v7).
  { apply Z.mod_small. subst v7 v6 v5 v4 v3 v2 v1.
    split; [repeat (apply Z.div_pos; [|lia]); lia|].
    repeat (apply Z.div_lt_upper_bound; [lia|]).
    change (2 ^ 64) with (256 * (256 * (256 * (256 * (256 * (256 * (256 * 256))))))) in Hv. lia. }
  rewrite E7.
  assert (R : forall x, x mod 256 = x - 256 * (x / 256))
    by (intros x; pose proof (Z.div_mod x 256 ltac:(lia)); lia).
  rewrite (R v), (R v1), (R v2), (R v3), (R v4), (R v5), (R v6).
  subst v7 v6 v5 v4 v3 v2 v1. lia.
Qed.

Lemma z64_eq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> (x / 2 ^ (8 * Z.of_nat k)) mod 256 = (y / 2 ^ (8 * Z.of_nat k)) mod 256) ->
  x = y.
Proof.
  intros x y Hx Hy H.
  pose proof (H 0%nat ltac:(lia)) as B0. pose proof (H 1%nat ltac:(lia)) as B1.
  pose proof (H 2%nat ltac:(lia)) as B2. pose proof (H 3%nat ltac:(lia)) as B3.
  pose proof (H 4%nat ltac:(lia)) as B4. pose proof (H 5%nat ltac:(lia)) as B5.
  pose proof (H 6%nat ltac:(lia)) as B6. pose proof (H 7%nat ltac:(lia)) as B7.
  replace (8 * Z.of_nat 0) with 0 in B0 by reflexivity.
  replace (8 * Z.of_nat 1) with 8 in B1 by reflexivity.
  replace (8 * Z.of_nat 2) with 16 in B2 by reflexivity.
  replace (8 * Z.of_nat 3) with 24 in B3 by reflexivity.
  replace (8 * Z.of_nat 4) with 32 in B4 by reflexivity.
  replace (8 * Z.of_nat 5) with 40 in B5 by reflexivity.
  replace (8 * Z.of_nat 6) with 48 in B6 by reflexivity.
  replace (8 * Z.of_nat 7) with 56 in B7 by reflexivity.
  rewrite <- (z64_bytes x Hx), <- (z64_bytes y Hy).
  rewrite B0, B1, B2, B3, B4, B5, B6, B7. reflexivity.
Qed.

(* `au64_at` fixes a pointer only modulo 2 ^ 64 (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a) *)
Lemma p_split : forall p v, p mod 2 ^ 64 = v -> p = v \/ 18446744073709551616 <= p \/ p < 0.
Proof.
  intros p v H.
  assert (Hpos : 0 < (2:Z) ^ 64) by (vm_compute; reflexivity).
  pose proof (Z.mod_pos_bound p (2 ^ 64) Hpos) as Hb. rewrite H in Hb.
  pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as D.
  set (q := p / 2 ^ 64) in D. rewrite H in D. rewrite E64 in D, Hb.
  destruct (Z.lt_trichotomy q 0) as [Hq|[Hq|Hq]]; [right; right | left | right; left]; lia.
Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) k x,
  nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  intros A l. induction l as [|a l IH]; intros k x H.
  - destruct k; discriminate.
  - destruct k as [|k].
    + cbn in H. injection H as <-. reflexivity.
    + cbn in H. cbn [skipn]. apply IH. exact H.
Qed.

Lemma nth_error_mapzb : forall (zs : list Z) i, (i < length zs)%nat ->
  nth_error (map zb zs) i = Some (zb (nth i zs 0)).
Proof.
  intros zs i Hi. rewrite nth_error_map. rewrite (nth_error_nth' zs 0) by exact Hi. reflexivity.
Qed.

Lemma nth_map_seq0 : forall {T} (f : nat -> T) W i (d : T), (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi.
  rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Lemma not_in_zb0 : forall zs, existsb (fun z => (z mod 256) =? 0) zs = false -> ~ In (zb 0) (map zb zs).
Proof.
  intros zs H Hin. apply in_map_iff in Hin as [z [Hz Hin]].
  assert (T : existsb (fun z => (z mod 256) =? 0) zs = true).
  { apply existsb_exists. exists z. split; [exact Hin|]. apply Z.eqb_eq.
    apply zb_mod in Hz. rewrite Hz. reflexivity. }
  congruence.
Qed.

(* the two memory bands, with the constants read through conversion only *)
Lemma amem_lo : forall p n, 0 <= p -> p + n <= 0x7fff7fff -> amem_range p n.
Proof.
  intros p n Hp Hn. unfold amem_range. left.
  assert (E : 0x7fff8000 <= kLowMemEnd) by (vm_compute; discriminate). lia.
Qed.

Lemma amem_hi : forall p n, 0x10007fff8000 <= p -> p + n <= 0x7ffffffffffe -> amem_range p n.
Proof.
  intros p n Hp Hn. unfold amem_range. right.
  assert (E1 : kHighMemBeg <= 0x10007fff8000) by (vm_compute; discriminate).
  assert (E2 : 0x7ffffffffffe <= kHighMemEnd - 1) by (vm_compute; discriminate).
  lia.
Qed.

(* ==========================================================================
   1. The witness memory
   ========================================================================== *)

Definition W_ODD : Z := 0x20fe0.                  (* odd[1]; odd[k] at W_ODD + 32 (k - 1) *)
Definition W_ERRNO : Z := 0x631b6c.
Definition W_REQ : Z := 0x7f0000002020.
Definition W_KB : Z := 0x602000000010.
Definition W_AB : Z := 0x602000000030.
Definition W_AL : Z := 0x211c0.                   (* texts[7] = "vlan", .rodata *)
Definition W_NAME : Z := LA_G_NAMES + 16.         (* g_names[2] = "nl2" *)
Definition SP_NT : Z := 0x7ffffffde000.
Definition SP_AR : Z := 0x7ffffffde100.
Definition SP_AW : Z := 0x7ffffffde100.

(* the three shadow bands, each with margin for the 8-aligned hull *)
Definition SH_LO : Z := 0x7fff7000.      Definition SH_LO_N : Z := 0xd2000.
Definition SH_HP : Z := 0xc047fff7000.   Definition SH_HP_N : Z := 0x2000.
Definition SH_RQ : Z := 0xfe07fff8000.   Definition SH_RQ_N : Z := 0x1000.

Definition w_sh (a : Z) : bool :=
  inrz a SH_LO SH_LO_N || inrz a SH_HP SH_HP_N || inrz a SH_RQ SH_RQ_N.

(* the 36-byte ACK chunk kernel() queued *)
Definition ack36 : list Z := [36;0;0;0; 2;0;0;0; 1;0;0;0] ++ repeat 0 24.

Definition dec_of (k : Z) : list Z := if k <? 10 then [48 + k] else [48 + k / 10; 48 + k mod 10].
Definition nlname (k : Z) : list Z := [110; 108] ++ dec_of k.

Definition odd_str (j : Z) : list Z :=
  if j =? 0 then [101;110;112;49;51;49;115;48;46;51;51]     (* enp131s0.33 *)
  else if j =? 1 then [101;116;104;48]                      (* eth0 *)
  else if j =? 2 then [119;108;97;110;48]                   (* wlan0 *)
  else [118;101;116;104;45;98;111;120].                     (* veth-box *)

Definition kof (j : Z) : Z := j + j / 15.
Definition ent_name_z (j : Z) : list Z := if j <? 60 then nlname (kof j) else odd_str (j - 60).
Definition ent_ptr (j : Z) : Z := if j <? 60 then LA_G_NAMES + 8 * kof j else W_ODD + 32 * (j - 60).
Definition ent_idx (j : Z) : Z := if j <? 60 then kof j + 2 else 101 + (j - 60).

Definition names_z (o : Z) : Z := nth (Z.to_nat (o mod 8)) (nlname (o / 8) ++ repeat 0 5) 0.
Definition odd_z (o : Z) : Z := nth (Z.to_nat (o mod 32)) (odd_str (o / 32) ++ repeat 0 32) 0.

Definition gnl_z (o : Z) : Z :=
  if o <? 36 then nth (Z.to_nat o) ack36 0
  else if o =? NK_N_CHUNKS then 1
  else if o =? NK_END_ERRNO then 105
  else if o =? NK_CHUNK_LEN then 36
  else if o =? NK_N_IF then 64
  else if inrz o NK_IF_NAME 512 then wle (ent_ptr ((o - NK_IF_NAME) / 8)) ((o - NK_IF_NAME) mod 8)
  else if inrz o NK_IF_INDEX 256 then wle (ent_idx ((o - NK_IF_INDEX) / 4)) ((o - NK_IF_INDEX) mod 4)
  else 0.

Definition req_z : list Z := [32;0;0;0; 18;0;1;0; 1;0;0;0; 0;0;0;0; 0;0;0;0; 4;0;0;0] ++ repeat 0 8.
Definition al_z : list Z := [118;108;97;110] ++ repeat 0 28.
Definition b16 : list Z := repeat 0x5a 16.
Definition name_z : list Z := [110;108;50].               (* "nl2" *)
Definition alias_z : list Z := [118;108;97;110].          (* "vlan" *)

Lemma name_lenm : Z.of_nat (length (map zb name_z)) = 3. Proof. reflexivity. Qed.
Lemma alias_lenm : Z.of_nat (length (map zb alias_z)) = 4. Proof. reflexivity. Qed.

Lemma req_z_is : map zb req_z = req_read 4.
Proof. vm_compute. reflexivity. Qed.

Definition w_obj (a : Z) : bool :=
  inrz a LA_G_NL NK_SIZE || inrz a LA_G_NAMES 512 || inrz a W_ODD 128 ||
  inrz a W_ERRNO 4 || inrz a W_REQ 32 || inrz a W_KB 17 || inrz a W_AB 17 || inrz a W_AL 32.

Definition wz (a : Z) : Z :=
  if inrz a LA_G_NL NK_SIZE then gnl_z (a - LA_G_NL)
  else if inrz a LA_G_NAMES 512 then names_z (a - LA_G_NAMES)
  else if inrz a W_ODD 128 then odd_z (a - W_ODD)
  else if inrz a W_REQ 32 then nth (Z.to_nat (a - W_REQ)) req_z 0
  else if inrz a W_KB 17 then 0x5a
  else if inrz a W_AB 17 then 0x5a
  else if inrz a W_AL 32 then nth (Z.to_nat (a - W_AL)) al_z 0
  else 0.

Definition wb (a : Z) : option byte :=
  if w_sh a then Some (zb 0) else if w_obj a then Some (zb (wz a)) else None.

Definition w_mem : word -> option byte := fun w => wb (bv_unsigned w).

Lemma w_sh_true_lo : forall a, SH_LO <= a < SH_LO + SH_LO_N -> w_sh a = true.
Proof. intros a Ha. unfold w_sh. rewrite (inrz_true a SH_LO SH_LO_N) by exact Ha. orbt. Qed.

Lemma w_sh_true_hp : forall a, SH_HP <= a < SH_HP + SH_HP_N -> w_sh a = true.
Proof. intros a Ha. unfold w_sh. rewrite (inrz_true a SH_HP SH_HP_N) by exact Ha. orbt. Qed.

Lemma w_sh_true_rq : forall a, SH_RQ <= a < SH_RQ + SH_RQ_N -> w_sh a = true.
Proof. intros a Ha. unfold w_sh. rewrite (inrz_true a SH_RQ SH_RQ_N) by exact Ha. orbt. Qed.

Lemma w_sh_false_lo : forall a, 0 <= a < SH_LO -> w_sh a = false.
Proof.
  intros a Ha. unfold w_sh.
  rewrite (inrz_false a SH_LO SH_LO_N) by lia.
  rewrite (inrz_false a SH_HP SH_HP_N) by (unfold SH_LO, SH_HP, SH_HP_N in *; lia).
  rewrite (inrz_false a SH_RQ SH_RQ_N) by (unfold SH_LO, SH_RQ, SH_RQ_N in *; lia).
  reflexivity.
Qed.

Lemma wb_sh : forall a, w_sh a = true -> wb a = Some (zb 0).
Proof. intros a H. unfold wb. rewrite H. reflexivity. Qed.

Lemma wb_val : forall a, w_sh a = false -> w_obj a = true -> wb a = Some (zb (wz a)).
Proof. intros a H1 H2. unfold wb. rewrite H1, H2. reflexivity. Qed.

Lemma wb_gnl : forall o, 0 <= o < NK_SIZE -> wb (LA_G_NL + o) = Some (zb (gnl_z o)).
Proof.
  intros o Ho. rewrite wb_val.
  - unfold wz. rewrite (inrz_true (LA_G_NL + o) LA_G_NL NK_SIZE) by lia.
    cbv beta iota. replace (LA_G_NL + o - LA_G_NL) with o by lia. reflexivity.
  - apply w_sh_false_lo. unfold LA_G_NL, NK_SIZE, SH_LO in *. lia.
  - unfold w_obj. rewrite (inrz_true (LA_G_NL + o) LA_G_NL NK_SIZE) by lia. orbt.
Qed.

(* ==========================================================================
   2. g_nl's 271992 bytes, as a byte FUNCTION of the offset
   ========================================================================== *)

Definition gnl_bs : list byte := map (fun i => zb (gnl_z (Z.of_nat i))) (seq 0 (Z.to_nat NK_SIZE)).

Lemma gnl_len_nat : length gnl_bs = Z.to_nat NK_SIZE.
Proof. unfold gnl_bs. rewrite length_map, length_seq. reflexivity. Qed.

Lemma gnl_len : Z.of_nat (length gnl_bs) = NK_SIZE.
Proof. rewrite gnl_len_nat. apply Z2Nat.id. unfold NK_SIZE. lia. Qed.

Lemma gnl_nth : forall i, (i < Z.to_nat NK_SIZE)%nat -> nth_error gnl_bs i = Some (zb (gnl_z (Z.of_nat i))).
Proof.
  intros i Hi. unfold gnl_bs. rewrite nth_error_map, nth_error_seq.
  replace (i <? Z.to_nat NK_SIZE)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add]. reflexivity.
Qed.

Lemma gnl_nth_off : forall o (j : nat), 0 <= o -> o + Z.of_nat j < NK_SIZE ->
  nth_error gnl_bs (Z.to_nat o + j)%nat = Some (zb (gnl_z (o + Z.of_nat j))).
Proof.
  intros o j Ho Hj. rewrite gnl_nth by lia.
  replace (Z.of_nat (Z.to_nat o + j)) with (o + Z.of_nat j)
    by (rewrite Nat2Z.inj_add, Z2Nat.id by lia; reflexivity).
  reflexivity.
Qed.

Lemma rdn4_of : forall (bs : list byte) (off : Z) (f : Z -> byte),
  (forall j, (j < 4)%nat -> nth_error bs (Z.to_nat off + j)%nat = Some (f (off + Z.of_nat j))) ->
  rdn bs off 4 = bytes_le_to_Z [f (off + 0); f (off + 1); f (off + 2); f (off + 3)].
Proof.
  intros bs off f H.
  pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1.
  pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
  replace (Z.of_nat 0) with 0 in H0 by reflexivity.
  replace (Z.of_nat 1) with 1 in H1 by reflexivity.
  replace (Z.of_nat 2) with 2 in H2 by reflexivity.
  replace (Z.of_nat 3) with 3 in H3 by reflexivity.
  replace (Z.to_nat off + 0)%nat with (Z.to_nat off) in H0 by lia.
  replace (Z.to_nat off + 1)%nat with (S (Z.to_nat off)) in H1 by lia.
  replace (Z.to_nat off + 2)%nat with (S (S (Z.to_nat off))) in H2 by lia.
  replace (Z.to_nat off + 3)%nat with (S (S (S (Z.to_nat off)))) in H3 by lia.
  unfold rdn, slice. change (Z.to_nat 4) with 4%nat.
  rewrite (skipn_nth_cons bs (Z.to_nat off) _ H0).
  rewrite (skipn_nth_cons bs (S (Z.to_nat off)) _ H1).
  rewrite (skipn_nth_cons bs (S (S (Z.to_nat off))) _ H2).
  rewrite (skipn_nth_cons bs (S (S (S (Z.to_nat off)))) _ H3).
  reflexivity.
Qed.

Lemma rdn8_of : forall (bs : list byte) (off : Z) (f : Z -> byte),
  (forall j, (j < 8)%nat -> nth_error bs (Z.to_nat off + j)%nat = Some (f (off + Z.of_nat j))) ->
  rdn bs off 8 = bytes_le_to_Z
    [f (off + 0); f (off + 1); f (off + 2); f (off + 3); f (off + 4); f (off + 5); f (off + 6); f (off + 7)].
Proof.
  intros bs off f H.
  pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1.
  pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
  pose proof (H 4%nat ltac:(lia)) as H4. pose proof (H 5%nat ltac:(lia)) as H5.
  pose proof (H 6%nat ltac:(lia)) as H6. pose proof (H 7%nat ltac:(lia)) as H7.
  replace (Z.of_nat 0) with 0 in H0 by reflexivity.
  replace (Z.of_nat 1) with 1 in H1 by reflexivity.
  replace (Z.of_nat 2) with 2 in H2 by reflexivity.
  replace (Z.of_nat 3) with 3 in H3 by reflexivity.
  replace (Z.of_nat 4) with 4 in H4 by reflexivity.
  replace (Z.of_nat 5) with 5 in H5 by reflexivity.
  replace (Z.of_nat 6) with 6 in H6 by reflexivity.
  replace (Z.of_nat 7) with 7 in H7 by reflexivity.
  replace (Z.to_nat off + 0)%nat with (Z.to_nat off) in H0 by lia.
  replace (Z.to_nat off + 1)%nat with (S (Z.to_nat off)) in H1 by lia.
  replace (Z.to_nat off + 2)%nat with (S (S (Z.to_nat off))) in H2 by lia.
  replace (Z.to_nat off + 3)%nat with (S (S (S (Z.to_nat off)))) in H3 by lia.
  replace (Z.to_nat off + 4)%nat with (S (S (S (S (Z.to_nat off))))) in H4 by lia.
  replace (Z.to_nat off + 5)%nat with (S (S (S (S (S (Z.to_nat off)))))) in H5 by lia.
  replace (Z.to_nat off + 6)%nat with (S (S (S (S (S (S (Z.to_nat off))))))) in H6 by lia.
  replace (Z.to_nat off + 7)%nat with (S (S (S (S (S (S (S (Z.to_nat off)))))))) in H7 by lia.
  unfold rdn, slice. change (Z.to_nat 8) with 8%nat.
  rewrite (skipn_nth_cons bs (Z.to_nat off) _ H0).
  rewrite (skipn_nth_cons bs (S (Z.to_nat off)) _ H1).
  rewrite (skipn_nth_cons bs (S (S (Z.to_nat off))) _ H2).
  rewrite (skipn_nth_cons bs (S (S (S (Z.to_nat off)))) _ H3).
  rewrite (skipn_nth_cons bs (S (S (S (S (Z.to_nat off))))) _ H4).
  rewrite (skipn_nth_cons bs (S (S (S (S (S (Z.to_nat off)))))) _ H5).
  rewrite (skipn_nth_cons bs (S (S (S (S (S (S (Z.to_nat off))))))) _ H6).
  rewrite (skipn_nth_cons bs (S (S (S (S (S (S (S (Z.to_nat off)))))))) _ H7).
  reflexivity.
Qed.

Lemma gnl_f4 : forall off, 0 <= off -> off + 4 <= NK_SIZE ->
  fld_u32 gnl_bs off = bytes_le_to_Z
    [zb (gnl_z (off+0)); zb (gnl_z (off+1)); zb (gnl_z (off+2)); zb (gnl_z (off+3))].
Proof.
  intros off Ho H4. unfold fld_u32.
  apply (rdn4_of gnl_bs off (fun x => zb (gnl_z x))).
  intros j Hj. apply gnl_nth_off; lia.
Qed.

Lemma gnl_f8 : forall off, 0 <= off -> off + 8 <= NK_SIZE ->
  fld_u64 gnl_bs off = bytes_le_to_Z
    [zb (gnl_z (off+0)); zb (gnl_z (off+1)); zb (gnl_z (off+2)); zb (gnl_z (off+3));
     zb (gnl_z (off+4)); zb (gnl_z (off+5)); zb (gnl_z (off+6)); zb (gnl_z (off+7))].
Proof.
  intros off Ho H8. unfold fld_u64.
  apply (rdn8_of gnl_bs off (fun x => zb (gnl_z x))).
  intros j Hj. apply gnl_nth_off; lia.
Qed.

Lemma k_n_chunks : nk_n_chunks gnl_bs = 1.
Proof. unfold nk_n_chunks. rewrite gnl_f4 by (unfold NK_N_CHUNKS, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_next : nk_next gnl_bs = 0.
Proof. unfold nk_next. rewrite gnl_f4 by (unfold NK_NEXT, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_end_errno : nk_end_errno gnl_bs = 105.
Proof. unfold nk_end_errno. rewrite gnl_f4 by (unfold NK_END_ERRNO, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_sock_errno : nk_socket_errno gnl_bs = 0.
Proof. unfold nk_socket_errno. rewrite gnl_f4 by (unfold NK_SOCKET_ERRNO, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_send_errno : nk_send_errno gnl_bs = 0.
Proof. unfold nk_send_errno. rewrite gnl_f4 by (unfold NK_SEND_ERRNO, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_open : nk_open gnl_bs = 0.
Proof. unfold nk_open. rewrite gnl_f4 by (unfold NK_OPEN, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_opened : nk_opened gnl_bs = 0.
Proof. unfold nk_opened. rewrite gnl_f4 by (unfold NK_OPENED, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_closed : nk_closed gnl_bs = 0.
Proof. unfold nk_closed. rewrite gnl_f4 by (unfold NK_CLOSED, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_misuse : nk_misuse gnl_bs = 0.
Proof. unfold nk_misuse. rewrite gnl_f4 by (unfold NK_MISUSE, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_n_sent : nk_n_sent gnl_bs = 0.
Proof. unfold nk_n_sent. rewrite gnl_f4 by (unfold NK_N_SENT, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_n_if : nk_n_if gnl_bs = 64.
Proof. unfold nk_n_if. rewrite gnl_f4 by (unfold NK_N_IF, NK_SIZE; lia). vm_compute. reflexivity. Qed.
Lemma k_chunk_len0 : fld_u64 gnl_bs (NK_CHUNK_LEN + 8 * 0) = 36.
Proof. rewrite gnl_f8 by (unfold NK_CHUNK_LEN, NK_SIZE; lia). vm_compute. reflexivity. Qed.

Lemma gnl_wf : nlk_wf gnl_bs.
Proof.
  unfold nlk_wf, NL_CHUNKS, NL_SENT_MAX, NL_CHUNK_MAX, NL_SENT_LEN.
  rewrite k_n_chunks, k_next, k_n_sent, k_n_if, k_open, k_opened, k_closed, k_misuse,
          k_end_errno, k_sock_errno, k_send_errno.
  repeat (match goal with |- _ /\ _ => split end); try lia.
  all: intros j Hj; try lia.
  all: assert (j = 0) by lia; subst j; rewrite k_chunk_len0; lia.
Qed.

(* ==========================================================================
   3. The 64 interface-table entries: ONE boolean check
   ========================================================================== *)

Definition bytes_eq (a : Z) (zs : list Z) : bool :=
  forallb (fun k => match wb (a + Z.of_nat k) with
                    | Some b => bv_unsigned b =? nth k zs 0
                    | None => false
                    end) (seq 0 (length zs)).

Lemma bytes_eq_sound : forall a zs, bytes_eq a zs = true ->
  forall k, (k < length zs)%nat -> wb (a + Z.of_nat k) = Some (zb (nth k zs 0)).
Proof.
  intros a zs H k Hk. unfold bytes_eq in H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_seq; lia)).
  destruct (wb (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate].
  apply Z.eqb_eq in H. rewrite <- H. unfold zb. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Definition ent_chk (i : nat) : bool :=
  (0 <? ent_ptr (Z.of_nat i)) &&
  (ent_ptr (Z.of_nat i) + Z.of_nat (length (ent_name_z (Z.of_nat i))) + 1 <=? 0x631b6c) &&
  (Z.of_nat (length (ent_name_z (Z.of_nat i))) <=? 11) &&
  (0 <=? ent_idx (Z.of_nat i)) &&
  (ent_idx (Z.of_nat i) <? 2 ^ 31) &&
  bytes_eq (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i)
           (map (fun k => wle (ent_ptr (Z.of_nat i)) (Z.of_nat k)) (seq 0 8)) &&
  bytes_eq (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i)
           (map (fun k => wle (ent_idx (Z.of_nat i)) (Z.of_nat k)) (seq 0 4)) &&
  bytes_eq (ent_ptr (Z.of_nat i)) (ent_name_z (Z.of_nat i) ++ [0]) &&
  negb (existsb (fun z => (z mod 256) =? 0) (ent_name_z (Z.of_nat i))) &&
  ((ent_ptr (Z.of_nat i) + Z.of_nat (length (ent_name_z (Z.of_nat i))) + 1 <=? LA_G_NL)
   || (LA_G_NL + NK_SIZE <=? ent_ptr (Z.of_nat i))).

Lemma ent_all : forallb ent_chk (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ent_ok : forall i, (i < 64)%nat -> ent_chk i = true.
Proof. intros i Hi. pose proof ent_all as A. rewrite forallb_forall in A. apply A, in_seq. lia. Qed.

Definition tabA : list (list byte * Z) :=
  map (fun i => (map zb (ent_name_z (Z.of_nat i)), ent_idx (Z.of_nat i))) (seq 0 64).

Lemma tabA_len : length tabA = 64%nat.
Proof. unfold tabA. rewrite length_map, length_seq. reflexivity. Qed.

Lemma tabA_nth : forall i nm ix, nth_error tabA i = Some (nm, ix) ->
  (i < 64)%nat /\ nm = map zb (ent_name_z (Z.of_nat i)) /\ ix = ent_idx (Z.of_nat i).
Proof.
  intros i nm ix H. unfold tabA in H. rewrite nth_error_map, nth_error_seq in H.
  destruct (Nat.ltb_spec i 64) as [Hlt|Hge]; [|cbn in H; discriminate].
  cbn [option_map Nat.add] in H. injection H as H1 H2.
  split; [lia | split; [symmetry; exact H1 | symmetry; exact H2]].
Qed.

(* ==========================================================================
   4. The memory facts, for every segment list
   ========================================================================== *)

Ltac wnum :=
  rewrite ?E64, ?E32, ?E31, ?NL_TALK_AK_val, ?REAC_LINK_ALIAS_READ_AK_val,
          ?REAC_LINK_ALIAS_WRITE_AK_val in *;
  cbv beta delta [apart_frame apart_gnl apart
                  LA_G_NL LA_G_NAMES NK_SIZE NK_IF_NAME NK_IF_INDEX NK_N_SENT
                  W_ODD W_ERRNO W_REQ W_KB W_AB W_AL W_NAME SP_NT SP_AR SP_AW] in *;
  lia.

Section W.
Variable segs : list Segment.

Lemma mb : forall a b, 0 <= a < 2 ^ 64 -> wb a = Some b -> mbyte segs w_mem a = Some b.
Proof.
  intros a b Ha H. unfold mbyte, w_mem. rewrite unsigned_lit_small by exact Ha.
  rewrite H. reflexivity.
Qed.

Lemma wr : forall a b, 0 <= a < 2 ^ 64 -> wb a = Some b -> writable_at segs w_mem a.
Proof.
  intros a b Ha H. unfold writable_at, wview, w_mem.
  rewrite unsigned_lit_small by exact Ha. rewrite H. cbv beta iota. discriminate.
Qed.

Lemma ard_sh : forall s, w_sh s = true -> 0 <= s < 2 ^ 64 -> ard segs w_mem s = Some 0.
Proof. intros s H Hs. unfold ard. rewrite (mb s (zb 0) Hs (wb_sh s H)). reflexivity. Qed.

Lemma ra_band : forall p n lo nn,
  0 <= lo -> lo + nn < 2 ^ 64 ->
  (forall s, lo <= s < lo + nn -> w_sh s = true) ->
  (forall x, p <= x < p + n -> lo <= SHADOW_OFF + x / 8 < lo + nn) ->
  range_addressable (ard segs w_mem) SHADOW_OFF p n.
Proof.
  intros p n lo nn Hl Hh Hb Hc x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. pose proof (Hc x Hx) as Hs.
  apply ard_sh; [apply Hb; exact Hs | lia].
Qed.

Lemma hull_band : forall p n lo nn,
  0 <= lo -> lo + nn < 2 ^ 64 ->
  (forall s, lo <= s < lo + nn -> w_sh s = true) ->
  lo + 7 <= shadow_addr p -> shadow_addr (p + n - 1) + 7 < lo + nn ->
  shadow_hull_vis (ard segs w_mem) p n.
Proof.
  intros p n lo nn Hl Hh Hb H1 H2 s Hs.
  pose proof (Z.div_mod (shadow_addr p) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (shadow_addr (p + n - 1)) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (shadow_addr (p + n - 1)) 8 ltac:(lia)) as M2.
  rewrite (ard_sh s); [discriminate | apply Hb; lia | lia].
Qed.

Lemma ra_lo : forall p n, 0 <= p -> p + n <= 0x640000 -> range_addressable (ard segs w_mem) SHADOW_OFF p n.
Proof.
  intros p n Hp Hn. apply (ra_band p n SH_LO SH_LO_N); try (unfold SH_LO, SH_LO_N; lia).
  - intros s Hs. apply w_sh_true_lo. exact Hs.
  - intros x Hx. unfold SHADOW_OFF, SH_LO, SH_LO_N.
    assert (0 <= x / 8) by (apply Z.div_pos; lia).
    assert (x / 8 < 0xc8000) by (apply Z.div_lt_upper_bound; lia).
    lia.
Qed.

Lemma hull_lo : forall p n, 0 <= p -> 0 < n -> p + n <= 0x640000 -> shadow_hull_vis (ard segs w_mem) p n.
Proof.
  intros p n Hp Hn Hpn. apply (hull_band p n SH_LO SH_LO_N); try (unfold SH_LO, SH_LO_N; lia).
  - intros s Hs. apply w_sh_true_lo. exact Hs.
  - unfold shadow_addr, SHADOW_OFF, SH_LO.
    assert (0 <= p / 8) by (apply Z.div_pos; lia). lia.
  - unfold shadow_addr, SHADOW_OFF, SH_LO, SH_LO_N.
    assert ((p + n - 1) / 8 < 0xc8000) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma ra_hp : forall p n, W_KB <= p -> p + n <= W_AB + 17 ->
  range_addressable (ard segs w_mem) SHADOW_OFF p n.
Proof.
  intros p n Hp Hn. apply (ra_band p n SH_HP SH_HP_N); try (unfold SH_HP, SH_HP_N; lia).
  - intros s Hs. apply w_sh_true_hp. exact Hs.
  - intros x Hx.
    assert (H1 : W_KB / 8 <= x / 8) by (apply Z.div_le_mono; unfold W_KB, W_AB in *; lia).
    assert (H2 : x / 8 <= (W_AB + 16) / 8) by (apply Z.div_le_mono; unfold W_KB, W_AB in *; lia).
    unfold W_KB in H1. unfold W_AB in H2.
    replace (0x602000000010 / 8) with 0xc0400000002 in H1 by reflexivity.
    replace ((0x602000000030 + 16) / 8) with 0xc0400000008 in H2 by reflexivity.
    unfold SHADOW_OFF, SH_HP, SH_HP_N. lia.
Qed.

Lemma hull_hp : forall p n, W_KB <= p -> 0 < n -> p + n <= W_AB + 17 ->
  shadow_hull_vis (ard segs w_mem) p n.
Proof.
  intros p n Hp Hn Hpn. apply (hull_band p n SH_HP SH_HP_N); try (unfold SH_HP, SH_HP_N; lia).
  - intros s Hs. apply w_sh_true_hp. exact Hs.
  - assert (H1 : W_KB / 8 <= p / 8) by (apply Z.div_le_mono; unfold W_KB, W_AB in *; lia).
    unfold W_KB in H1. replace (0x602000000010 / 8) with 0xc0400000002 in H1 by reflexivity.
    unfold shadow_addr, SHADOW_OFF, SH_HP. lia.
  - assert (H2 : (p + n - 1) / 8 <= (W_AB + 16) / 8)
      by (apply Z.div_le_mono; unfold W_KB, W_AB in *; lia).
    unfold W_AB in H2. replace ((0x602000000030 + 16) / 8) with 0xc0400000008 in H2 by reflexivity.
    unfold shadow_addr, SHADOW_OFF, SH_HP, SH_HP_N. lia.
Qed.

Lemma ra_rq : forall p n, W_REQ <= p -> p + n <= W_REQ + 32 ->
  range_addressable (ard segs w_mem) SHADOW_OFF p n.
Proof.
  intros p n Hp Hn. apply (ra_band p n SH_RQ SH_RQ_N); try (unfold SH_RQ, SH_RQ_N; lia).
  - intros s Hs. apply w_sh_true_rq. exact Hs.
  - intros x Hx.
    assert (H1 : W_REQ / 8 <= x / 8) by (apply Z.div_le_mono; unfold W_REQ in *; lia).
    assert (H2 : x / 8 <= (W_REQ + 31) / 8) by (apply Z.div_le_mono; unfold W_REQ in *; lia).
    unfold W_REQ in H1, H2.
    replace (0x7f0000002020 / 8) with 0xfe000000404 in H1 by reflexivity.
    replace ((0x7f0000002020 + 31) / 8) with 0xfe000000407 in H2 by reflexivity.
    unfold SHADOW_OFF, SH_RQ, SH_RQ_N. lia.
Qed.

Lemma hull_rq : forall p n, W_REQ <= p -> 0 < n -> p + n <= W_REQ + 32 ->
  shadow_hull_vis (ard segs w_mem) p n.
Proof.
  intros p n Hp Hn Hpn. apply (hull_band p n SH_RQ SH_RQ_N); try (unfold SH_RQ, SH_RQ_N; lia).
  - intros s Hs. apply w_sh_true_rq. exact Hs.
  - assert (H1 : W_REQ / 8 <= p / 8) by (apply Z.div_le_mono; unfold W_REQ in *; lia).
    unfold W_REQ in H1. replace (0x7f0000002020 / 8) with 0xfe000000404 in H1 by reflexivity.
    unfold shadow_addr, SHADOW_OFF, SH_RQ. lia.
  - assert (H2 : (p + n - 1) / 8 <= (W_REQ + 31) / 8)
      by (apply Z.div_le_mono; unfold W_REQ in *; lia).
    unfold W_REQ in H2. replace ((0x7f0000002020 + 31) / 8) with 0xfe000000407 in H2 by reflexivity.
    unfold shadow_addr, SHADOW_OFF, SH_RQ, SH_RQ_N. lia.
Qed.

(* ---- bytes, writability and little-endian values from a boolean check ---- *)

Lemma abytes_ofn : forall a zs n, bytes_eq a zs = true -> Z.of_nat (length zs) = n ->
  0 <= a -> a + n <= 2 ^ 64 -> abytes segs w_mem a (map zb zs).
Proof.
  intros a zs n H Hn Ha Hb. unfold abytes. rewrite length_map, Hn.
  split; [exact Ha|]. split; [exact Hb|].
  intros i Hi.
  rewrite nth_error_mapzb by exact Hi.
  apply mb; [lia | apply bytes_eq_sound; [exact H | exact Hi]].
Qed.

Lemma awrange_ofn : forall a zs n, bytes_eq a zs = true -> Z.of_nat (length zs) = n ->
  0 <= a -> a + n <= 2 ^ 64 -> awrange segs w_mem a n.
Proof.
  intros a zs n H Hn Ha Hb i Hi.
  replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  eapply wr; [lia | apply bytes_eq_sound; [exact H | lia]].
Qed.

Lemma au8_ofn : forall a zs n, bytes_eq a zs = true -> Z.of_nat (length zs) = n ->
  0 <= a -> a + n <= 2 ^ 64 -> au8arr segs w_mem a (map zb zs).
Proof.
  intros a zs n H Hn Ha Hb. split.
  - apply (abytes_ofn a zs n); assumption.
  - rewrite length_map, Hn. apply (awrange_ofn a zs n); assumption.
Qed.

Lemma abuf_ofn : forall a zs n, bytes_eq a zs = true -> Z.of_nat (length zs) = n ->
  0 <= a -> a + n <= 2 ^ 64 -> abuf segs w_mem a n.
Proof.
  intros a zs n H Hn Ha Hb. exists (map zb zs). rewrite length_map.
  split; [exact Hn | apply (au8_ofn a zs n); assumption].
Qed.

Lemma acstr_ofn : forall a zs n, bytes_eq a (zs ++ [0]) = true -> Z.of_nat (length zs) = n ->
  0 <= a -> a + n + 1 <= 2 ^ 64 ->
  existsb (fun z => (z mod 256) =? 0) zs = false ->
  acstr_at segs w_mem a (map zb zs).
Proof.
  intros a zs n H Hn Ha Hb Hz. split.
  - replace (map zb zs ++ [zb 0]) with (map zb (zs ++ [0])) by (rewrite map_app; reflexivity).
    apply (abytes_ofn a (zs ++ [0]) (n + 1)); [exact H | | exact Ha | lia].
    rewrite length_app. cbn [length]. lia.
  - apply not_in_zb0. exact Hz.
Qed.

Lemma val_of : forall a v (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  0 <= v < 2 ^ (8 * Z.of_nat n) ->
  bytes_eq a (map (fun k => wle v (Z.of_nat k)) (seq 0 n)) = true ->
  val_mem segs w_mem a n v.
Proof.
  intros a v n Ha Hb Hv H k Hk.
  assert (Hlen : length (map (fun k => wle v (Z.of_nat k)) (seq 0 n)) = n)
    by (rewrite length_map, length_seq; reflexivity).
  pose proof (bytes_eq_sound _ _ H k ltac:(lia)) as E.
  assert (Hr : 0 <= a + Z.of_nat k < 2 ^ 64) by (clear - Ha Hb Hk; lia).
  rewrite (mb _ _ Hr E). f_equal.
  rewrite (nth_map_seq0 (fun k0 => wle v (Z.of_nat k0)) n k 0 Hk).
  rewrite le_byte_div, (Z.mod_small v (2 ^ (8 * Z.of_nat n))) by exact Hv.
  unfold zb, wle. reflexivity.
Qed.

Lemma val_mem_inj64 : forall a p v, 0 <= v < 2 ^ 64 ->
  val_mem segs w_mem a 8 p -> val_mem segs w_mem a 8 v -> p mod 2 ^ 64 = v.
Proof.
  intros a p v Hv H1 H2.
  assert (Hpos : 0 < (2:Z) ^ 64) by (vm_compute; reflexivity).
  pose proof (Z.mod_pos_bound p (2 ^ 64) Hpos) as Hb.
  apply z64_eq; [exact Hb | exact Hv|].
  intros k Hk. specialize (H1 k Hk). specialize (H2 k Hk).
  rewrite H1 in H2. apply some_inj in H2. apply zb_mod in H2.
  rewrite !le_byte_div in H2.
  rewrite !Z.mod_mod in H2 by lia.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in H2.
  rewrite (Z.mod_small v (2 ^ 64)) in H2 by exact Hv.
  exact H2.
Qed.

(* ---- g_nl, the table, and the small objects at the witness memory ---- *)

Lemma gnl_anlk : anlk_at segs w_mem LA_G_NL gnl_bs.
Proof.
  split; [|exact gnl_len]. split.
  - unfold abytes. split; [unfold LA_G_NL; lia|].
    split; [rewrite gnl_len; wnum|].
    intros i Hi. rewrite gnl_len_nat in Hi.
    rewrite gnl_nth by exact Hi.
    apply mb; [wnum | apply wb_gnl; lia].
  - rewrite gnl_len. intros i Hi.
    eapply wr; [wnum | apply wb_gnl; lia].
Qed.

Lemma ent_facts : forall (i : nat), (i < 64)%nat ->
  0 < ent_ptr (Z.of_nat i) /\
  ent_ptr (Z.of_nat i) + Z.of_nat (length (ent_name_z (Z.of_nat i))) + 1 <= 0x631b6c /\
  Z.of_nat (length (ent_name_z (Z.of_nat i))) <= 11 /\
  0 <= ent_idx (Z.of_nat i) < 2 ^ 31 /\
  au64_at segs w_mem (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (ent_ptr (Z.of_nat i)) /\
  au32_at segs w_mem (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i) (ent_idx (Z.of_nat i)) /\
  acstr_at segs w_mem (ent_ptr (Z.of_nat i)) (map zb (ent_name_z (Z.of_nat i))) /\
  (ent_ptr (Z.of_nat i) + Z.of_nat (length (ent_name_z (Z.of_nat i))) + 1 <= LA_G_NL
   \/ LA_G_NL + NK_SIZE <= ent_ptr (Z.of_nat i)).
Proof.
  intros i Hi. pose proof (ent_ok i Hi) as H. unfold ent_chk in H.
  apply andb_prop in H as [H HA]. apply andb_prop in H as [H H9].
  apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply negb_true_iff in H9.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [lia|].
  split.
  { unfold au64_at. apply (val_of _ _ 8%nat); [wnum | wnum | | exact H6].
    change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). wnum. }
  split.
  { unfold au32_at. apply (val_of _ _ 4%nat); [wnum | wnum | | exact H7].
    change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). wnum. }
  split.
  { apply (acstr_ofn _ _ (Z.of_nat (length (ent_name_z (Z.of_nat i)))));
      [exact H8 | reflexivity | wnum | wnum | exact H9]. }
  apply orb_prop in HA. destruct HA as [HA|HA];
    [left; apply Z.leb_le; exact HA | right; apply Z.leb_le; exact HA].
Qed.

Lemma gnl_iftab : aiftab_at segs w_mem LA_G_NL gnl_bs tabA.
Proof.
  split; [rewrite k_n_if, tabA_len; reflexivity|].
  split; [rewrite tabA_len; lia|].
  intros i nm ix Ht.
  destruct (tabA_nth i nm ix Ht) as (Hi & -> & ->).
  destruct (ent_facts i Hi) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  split; [exact F4|].
  exists (ent_ptr (Z.of_nat i)).
  split; [exact F5|]. split; [lia|]. split; [exact F7 | exact F6].
Qed.

Lemma tab_clause : forall (i : nat) nm ix p,
  nth_error tabA i = Some (nm, ix) ->
  au64_at segs w_mem (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  (p = ent_ptr (Z.of_nat i) \/ 18446744073709551616 <= p \/ p < 0) /\
  0 < ent_ptr (Z.of_nat i) /\
  ent_ptr (Z.of_nat i) + Z.of_nat (length nm) + 1 <= 0x631b6c /\
  Z.of_nat (length nm) <= 11 /\
  (ent_ptr (Z.of_nat i) + Z.of_nat (length nm) + 1 <= LA_G_NL
   \/ LA_G_NL + NK_SIZE <= ent_ptr (Z.of_nat i)).
Proof.
  intros i nm ix p Ht Hp.
  destruct (tabA_nth i nm ix Ht) as (Hi & -> & ->).
  destruct (ent_facts i Hi) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  rewrite length_map.
  split; [|split; [exact F1 | split; [exact F2 | split; [exact F3 | exact F8]]]].
  apply (p_split p (ent_ptr (Z.of_nat i))).
  apply (val_mem_inj64 (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p (ent_ptr (Z.of_nat i)));
    [wnum | exact Hp | exact F5].
Qed.

(* the small objects *)
Lemma errno_wr : awrange segs w_mem 0x631b6c 4.
Proof. apply (awrange_ofn _ [0;0;0;0] 4); [vm_compute; reflexivity | reflexivity | wnum | wnum]. Qed.

Lemma req_bytes : abytes segs w_mem W_REQ (map zb req_z).
Proof. apply (abytes_ofn _ req_z 32); [vm_compute; reflexivity | reflexivity | wnum | wnum]. Qed.

Lemma kb_buf : abuf segs w_mem W_KB 16.
Proof. apply (abuf_ofn _ b16 16); [vm_compute; reflexivity | reflexivity | wnum | wnum]. Qed.

Lemma ab_buf : abuf segs w_mem W_AB 16.
Proof. apply (abuf_ofn _ b16 16); [vm_compute; reflexivity | reflexivity | wnum | wnum]. Qed.

Lemma name_str : acstr_at segs w_mem W_NAME (map zb name_z).
Proof.
  apply (acstr_ofn _ name_z 3); [vm_compute; reflexivity | reflexivity | wnum | wnum
    | vm_compute; reflexivity].
Qed.

Lemma alias_str : acstr_at segs w_mem W_AL (map zb alias_z).
Proof.
  apply (acstr_ofn _ alias_z 4); [vm_compute; reflexivity | reflexivity | wnum | wnum
    | vm_compute; reflexivity].
Qed.

Lemma alias_slack : abytes segs w_mem (W_AL + 5) (map zb [0;0;0]).
Proof. apply (abytes_ofn _ [0;0;0] 3); [vm_compute; reflexivity | reflexivity | wnum | wnum]. Qed.

(* the tail of a string's 8-byte granule after its NUL (the strcmp contract's `atail_vis`): visible when the string
   starts 8-aligned in g_names or in the odd strings' slots, is at most 11 bytes long, and its granule tail stays
   inside the object (the witness holds the whole object's bytes) *)
Lemma w_obj_names : forall x, LA_G_NAMES <= x < LA_G_NAMES + 512 -> w_obj x = true.
Proof. intros x Hx. unfold w_obj. rewrite (inrz_true x LA_G_NAMES 512) by exact Hx. orbt. Qed.

Lemma w_obj_odd : forall x, W_ODD <= x < W_ODD + 128 -> w_obj x = true.
Proof. intros x Hx. unfold w_obj. rewrite (inrz_true x W_ODD 128) by exact Hx. orbt. Qed.

Lemma vis_obj : forall a, 0 <= a < SH_LO -> w_obj a = true -> ard segs w_mem a <> None.
Proof.
  intros a Ha Ho. unfold ard.
  assert (Hm : 0 <= a < 2 ^ 64) by (rewrite E64; unfold SH_LO in Ha; lia).
  rewrite (mb a (zb (wz a)) Hm (wb_val a (w_sh_false_lo a Ha) Ho)). cbv [option_map]. discriminate.
Qed.

Lemma obj_tail : forall lo nn p n a,
  (forall x, lo <= x < lo + nn -> w_obj x = true) -> 0 <= lo -> lo <= p -> p + 16 <= lo + nn -> lo + nn <= SH_LO ->
  p mod 8 = 0 -> 0 <= n <= 11 -> p + n < a < p + n - (p + n) mod 8 + 8 -> ard segs w_mem a <> None.
Proof.
  intros lo nn p n a Hw Hlo Hp Hpn Hsh Hal Hn Ha.
  assert (Hlt : a < p + 16).
  { pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hb.
    pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as Hd.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Hd0. rewrite Hal in Hd0.
    assert (Hq : (p + n) / 8 <= p / 8 + 1) by lia. lia. }
  apply vis_obj; [lia|]. apply Hw. lia.
Qed.

Lemma name_tail : forall a, W_NAME + 3 < a < W_NAME + 3 - (W_NAME + 3) mod 8 + 8 -> ard segs w_mem a <> None.
Proof.
  intros a Ha. apply (obj_tail LA_G_NAMES 512 W_NAME 3 a w_obj_names);
    try (unfold W_NAME, LA_G_NAMES, SH_LO; lia); try exact Ha; reflexivity.
Qed.

Lemma ent_tail : forall (i : nat) nm ix a, nth_error tabA i = Some (nm, ix) ->
  ent_ptr (Z.of_nat i) + Z.of_nat (length nm) < a
    < ent_ptr (Z.of_nat i) + Z.of_nat (length nm) - (ent_ptr (Z.of_nat i) + Z.of_nat (length nm)) mod 8 + 8 ->
  ard segs w_mem a <> None.
Proof.
  intros i nm ix a Ht Ha.
  destruct (tabA_nth i nm ix Ht) as (Hi & Hnm & _). subst nm. rewrite length_map in Ha.
  destruct (ent_facts i Hi) as (_ & _ & F3 & _).
  revert Ha F3. unfold ent_ptr. destruct (Z.of_nat i <? 60) eqn:E; intros Ha F3.
  - apply Z.ltb_lt in E.
    assert (Hk : 0 <= kof (Z.of_nat i) <= 62) by (unfold kof; lia).
    apply (obj_tail LA_G_NAMES 512 (LA_G_NAMES + 8 * kof (Z.of_nat i))
             (Z.of_nat (length (ent_name_z (Z.of_nat i)))) a w_obj_names);
      try (unfold LA_G_NAMES, SH_LO in *; lia); exact Ha.
  - apply Z.ltb_ge in E.
    apply (obj_tail W_ODD 128 (W_ODD + 32 * (Z.of_nat i - 60))
             (Z.of_nat (length (ent_name_z (Z.of_nat i)))) a w_obj_odd);
      try (unfold W_ODD, SH_LO in *; lia); exact Ha.
Qed.

End W.

(* ==========================================================================
   5. The three lemmas
   ========================================================================== *)

Lemma nl_talk_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = 0x631b6c -> as_tp B = 0x631c10 ->
  aarg regs 0 = W_REQ -> aarg regs 1 = 32 -> aarg regs 2 = W_KB -> aarg regs 3 = 16 ->
  aarg regs 4 = W_AB -> aarg regs 5 = 16 -> spZ regs = SP_NT ->
  nl_talk_apre segs B regs w_mem.
Proof.
  intros segs B regs He Ht A0 A1 A2 A3 A4 A5 Hsp.
  unfold nl_talk_apre. rewrite He, A0, A1, A2, A3, A4, A5.
  exists gnl_bs, (map zb req_z).
  split; [apply gnl_anlk|].
  split; [exact gnl_wf|].
  split; [exact k_open|].
  split; [rewrite k_opened; wnum|].
  split; [rewrite k_closed; wnum|].
  split; [apply ra_lo; wnum|].
  split; [apply hull_lo; wnum|].
  split.
  { unfold aerrno_ok. rewrite He, Ht.
    split; [reflexivity|].
    split; [apply errno_wr|].
    split; [apply ra_lo; wnum|].
    split; [wnum|]. wnum. }
  split; [apply req_bytes|].
  split; [rewrite length_map; reflexivity|].
  split; [unfold NL_SENT_LEN; lia|].
  split; [apply amem_hi; wnum|].
  split; [apply ra_rq; wnum|].
  split; [intros _; apply hull_rq; wnum|].
  split; [wnum|].
  split; [wnum|].
  split; [intros _ _; apply kb_buf|].
  split; [intros _ _; apply ab_buf|].
  split; [intros _; wnum|].
  split; [intros _; wnum|].
  split; [intros _ _ _ _; wnum|].
  split; [intros _; split; wnum|].
  split; [intros _; split; wnum|].
  split; [intros _ _; unfold achk; split; [apply amem_hi; wnum|];
          split; [apply ra_hp; wnum | apply hull_hp; wnum]|].
  intros _ _. unfold achk. split; [apply amem_hi; wnum|].
  split; [apply ra_hp; wnum | apply hull_hp; wnum].
Qed.

Lemma reac_link_alias_read_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = 0x631b6c -> as_tp B = 0x631c10 ->
  aarg regs 0 = W_NAME -> aarg regs 1 = W_KB -> aarg regs 2 = 16 ->
  aarg regs 3 = W_AB -> aarg regs 4 = 16 -> spZ regs = SP_AR ->
  reac_link_alias_read_apre segs B regs w_mem.
Proof.
  intros segs B regs He Ht A0 A1 A2 A3 A4 Hsp.
  unfold reac_link_alias_read_apre. rewrite He, A0, A1, A2, A3, A4.
  exists gnl_bs, tabA, (Some (map zb name_z)).
  split; [apply gnl_anlk|].
  split; [exact gnl_wf|].
  split; [exact k_open|].
  split; [rewrite k_opened; wnum|].
  split; [rewrite k_closed; wnum|].
  split; [apply gnl_iftab|].
  split; [apply ra_lo; wnum|].
  split; [apply hull_lo; wnum|].
  split.
  { unfold aerrno_ok. rewrite He, Ht.
    split; [reflexivity|].
    split; [apply errno_wr|].
    split; [apply ra_lo; wnum|].
    split; [wnum|]. wnum. }
  split; [split; [wnum | apply name_str]|].
  split; [intros _ _; apply kb_buf|].
  split; [intros _ _; apply ab_buf|].
  (* the interface-table strings *)
  split.
  { intros i nm ix p Ht' Hp.
    destruct (tab_clause segs i nm ix p Ht' Hp) as (Hc & Hpos & Hlt & Hle & Hgn).
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [intros _ _; destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [intros _ _; destruct Hc as [->|[Hc|Hc]]; wnum|].
    intros Hr.
    assert (Hpe : p = ent_ptr (Z.of_nat i))
      by (destruct Hc as [Hc|[Hc|Hc]]; [exact Hc | wnum | wnum]).
    subst p. split; [exact Hpos|]. split; [wnum|].
    split; [unfold achk; split; [apply amem_lo; wnum|];
            split; [apply ra_lo; wnum | apply hull_lo; wnum]|].
    intros a Ha. exact (ent_tail segs i nm ix a Ht' Ha). }
  split.
  { intros s Hs. apply some_inj in Hs. subst s. rewrite name_lenm.
    split; [intros _ _; wnum | intros _ _; wnum]. }
  split; [intros _ _ _ _; wnum|].
  split; [intros _; wnum|].
  split; [intros _; wnum|].
  split.
  { intros s Hs. apply some_inj in Hs. subst s. rewrite name_lenm.
    split; [wnum|]. split; [wnum|]. split; [wnum|].
    split; [unfold achk; split; [apply amem_lo; wnum|];
            split; [apply ra_lo; wnum | apply hull_lo; wnum]|].
    intros a Ha. exact (name_tail segs a Ha). }
  split; [intros _; split; wnum|].
  split; [intros _; split; wnum|].
  split; [intros _ _; unfold achk; split; [apply amem_hi; wnum|];
          split; [apply ra_hp; wnum | apply hull_hp; wnum]|].
  intros _ _. unfold achk. split; [apply amem_hi; wnum|].
  split; [apply ra_hp; wnum | apply hull_hp; wnum].
Qed.

Lemma reac_link_alias_write_apre_sat : forall segs (B : asyms) (regs : bvmap 5 word),
  as_errno B = 0x631b6c -> as_tp B = 0x631c10 ->
  aarg regs 0 = W_NAME -> aarg regs 1 = W_AL -> spZ regs = SP_AW ->
  reac_link_alias_write_apre segs B regs w_mem.
Proof.
  intros segs B regs He Ht A0 A1 Hsp.
  unfold reac_link_alias_write_apre. rewrite He, A0, A1.
  exists gnl_bs, tabA, (Some (map zb name_z)), (Some (map zb alias_z)).
  split; [apply gnl_anlk|].
  split; [exact gnl_wf|].
  split; [exact k_open|].
  split; [rewrite k_opened; wnum|].
  split; [rewrite k_closed; wnum|].
  split; [apply gnl_iftab|].
  split; [apply ra_lo; wnum|].
  split; [apply hull_lo; wnum|].
  split.
  { unfold aerrno_ok. rewrite He, Ht.
    split; [reflexivity|].
    split; [apply errno_wr|].
    split; [apply ra_lo; wnum|].
    split; [wnum|]. wnum. }
  split; [split; [wnum | apply name_str]|].
  split; [split; [wnum | apply alias_str]|].
  split.
  { intros i nm ix p Ht' Hp.
    destruct (tab_clause segs i nm ix p Ht' Hp) as (Hc & Hpos & Hlt & Hle & Hgn).
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    split; [destruct Hc as [->|[Hc|Hc]]; wnum|].
    intros Hr.
    assert (Hpe : p = ent_ptr (Z.of_nat i))
      by (destruct Hc as [Hc|[Hc|Hc]]; [exact Hc | wnum | wnum]).
    subst p. split; [exact Hpos|]. split; [wnum|].
    split; [unfold achk; split; [apply amem_lo; wnum|];
            split; [apply ra_lo; wnum | apply hull_lo; wnum]|].
    intros a Ha. exact (ent_tail segs i nm ix a Ht' Ha). }
  split.
  { intros s Hs. apply some_inj in Hs. subst s. rewrite name_lenm.
    split; [wnum|]. split; [wnum|]. split; [wnum|].
    split; [unfold achk; split; [apply amem_lo; wnum|];
            split; [apply ra_lo; wnum | apply hull_lo; wnum]|].
    intros a Ha. exact (name_tail segs a Ha). }
  split.
  { intros s Hs. apply some_inj in Hs. subst s. rewrite alias_lenm.
    split; [wnum|]. split; [wnum|]. split; [wnum|].
    unfold achk. split; [apply amem_lo; wnum|].
    split; [apply ra_lo; wnum | apply hull_lo; wnum]. }
  intros s Hs. apply some_inj in Hs. subst s. exists (map zb [0;0;0]).
  rewrite alias_lenm. split.
  - replace (W_AL + 4 + 1) with (W_AL + 5) by lia. apply alias_slack.
  - assert (E : (- (W_AL + 4 + 1)) mod 8 = 3) by reflexivity.
    rewrite E. rewrite length_map. cbn [length]. lia.
Qed.
