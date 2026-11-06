(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSat.v at b08119c041c; the same witness for
   image B (fuzz_role.asan-ubsan) on lib/AU/Img0.v's rsegs: image B's globals table 0x9f380, its registration words,
   its nine strings, its five read-only doubles, its refuse table 0x9a920 and its eleven callee entries
   (pod_write_ent is added: image B calls it out of line). *)
(* Image B's witnesses for the memory premises of reac-pw/fuzz_role's callee contracts (lib/A/RPgCSpec.v). At the
   pinned image, one concrete pair (H_w, mem_w) satisfies every string premise (RPgBase.rl_cstr), the read-only
   constant premise (RPgBase.rl_ro_cells) and reac_role_refuse_code's table premises at the image's measured
   addresses, and each callee entry holds its measured first instruction, so those contracts are not vacuous on
   image B. Every address, byte and descriptor field below is checked against the image's loaded segments by
   computation.
   Pinned image: fuzz_role.asan-ubsan, sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0
   (the unstripped twin dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a holds the same bytes here).
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* Image B: the loaded segments elf-snapshot makes of the pinned fuzz_role.asan-ubsan (lib/AU/Img0.v). *)
Definition segsB : list Segment := rsegs.

(* ================================ boolean checkers and their soundness ================================ *)
Definition oz_eqb (o : option Z) (v : Z) : bool := match o with Some z => z =? v | None => false end.
Lemma oz_eqb_ok : forall o v, oz_eqb o v = true -> o = Some v.
Proof. intros [z|] v H; cbn [oz_eqb] in H; [apply Z.eqb_eq in H; subst z; reflexivity | discriminate H]. Qed.

Definition is_someb {A : Type} (o : option A) : bool := match o with Some _ => true | None => false end.
Lemma is_someb_ok : forall (A : Type) (o : option A), is_someb o = true -> o <> None.
Proof. intros A [x|] H; cbn [is_someb] in H; [discriminate | discriminate H]. Qed.

Lemma forallb_seq : forall (f : nat -> bool) (n : nat), forallb f (seq 0 n) = true -> forall k, (k < n)%nat -> f k = true.
Proof. intros f n H k Hk. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

(* The bytes l at a, read by rd. *)
Definition bytes_chk (rd : reader) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (rd (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
Lemma bytes_chk_ok : forall rd a l, bytes_chk rd a l = true ->
  forall i, 0 <= i < Z.of_nat (length l) -> rd (a + i) = Some (nth (Z.to_nat i) l 0).
Proof.
intros rd a l Hc i Hi. unfold bytes_chk in Hc. assert (Hk : (Z.to_nat i < length l)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
exact (oz_eqb_ok _ _ E).
Qed.

Lemma bytes_range_ok : forall l, forallb (fun b => (0 <? b) && (b <? 256)) l = true -> Forall (fun b => 0 < b < 256) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. cbv beta. rewrite forallb_forall in H. specialize (H b Hb). cbv beta in H.
apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* a lies in a loaded segment (YG0d.in_img). *)
Definition in_imgb (segs : list Segment) (a : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma in_imgb_ok : forall segs a, in_imgb segs a = true -> in_img segs a.
Proof.
intros segs a H. unfold in_imgb in H. apply existsb_exists in H. destruct H as (sg & Hin & Hb). cbv beta in Hb.
apply andb_prop in Hb. destruct Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold in_img. exists sg. split; [exact Hin | lia].
Qed.
Definition img_chk (segs : list Segment) (a : Z) (n : nat) : bool := forallb (fun k => in_imgb segs (a + Z.of_nat k)) (seq 0 n).
Lemma img_chk_ok : forall segs a n, img_chk segs a n = true -> forall i, 0 <= i < Z.of_nat n -> in_img segs (a + i).
Proof.
intros segs a n Hc i Hi. unfold img_chk in Hc. assert (Hk : (Z.to_nat i < n)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
exact (in_imgb_ok _ _ E).
Qed.

Definition amem_rangeb (p n : Z) : bool :=
  (p + n <=? kLowMemEnd - 1) || ((kHighMemBeg <=? p) && (p + n <=? kHighMemEnd - 1)).
Lemma amem_rangeb_ok : forall p n, amem_rangeb p n = true -> amem_range p n.
Proof.
intros p n H. unfold amem_rangeb in H. unfold amem_range. apply orb_true_iff in H.
destruct H as [H|H]; [left; apply Z.leb_le; exact H|].
right. apply andb_prop in H. destruct H as [H1 H2]. split; [apply Z.leb_le; exact H1 | apply Z.leb_le; exact H2].
Qed.

(* YG0v.range_addressable over the n bytes at a. *)
Definition saddr_okb (x s : Z) : bool := (s =? 0) || ((x mod 8 <? s) && (s <? 8)).
Lemma saddr_okb_ok : forall x s, saddr_okb x s = true -> saddr_ok x s.
Proof.
intros x s H. unfold saddr_okb in H. unfold saddr_ok. apply orb_true_iff in H.
destruct H as [H|H]; [left; apply Z.eqb_eq; exact H|].
right. apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. split; assumption.
Qed.
Definition ra_chk (rd : reader) (B a : Z) (n : nat) : bool :=
  forallb (fun k => match rd (shadow_of_addr B (a + Z.of_nat k)) with
                    | Some s => saddr_okb (a + Z.of_nat k) s
                    | None => false
                    end) (seq 0 n).
Lemma ra_chk_ok : forall rd B a n len, Z.of_nat n = len -> ra_chk rd B a n = true -> range_addressable rd B a len.
Proof.
intros rd B a n len Hn Hc. unfold range_addressable. intros x Hx. unfold ra_chk in Hc.
assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (a + (x - a)) with x in E by ring.
revert E. destruct (rd (shadow_of_addr B x)) as [v|]; cbv beta iota; intros E; [|discriminate E].
exists v. split; [reflexivity | exact (saddr_okb_ok _ _ E)].
Qed.

(* YG0d.shadow_hull_vis: every shadow byte of the 8-aligned hull of the shadow of [x, x + n) is readable. *)
Definition hull_chk (rd : reader) (x n : Z) : bool :=
  forallb (fun k => is_someb (rd (shadow_addr x / 8 * 8 + Z.of_nat k)))
    (seq 0 (Z.to_nat (shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8))).
Lemma hull_chk_ok : forall rd x n, hull_chk rd x n = true -> shadow_hull_vis rd x n.
Proof.
intros rd x n Hc. unfold shadow_hull_vis. intros s Hs. unfold hull_chk in Hc.
set (lo := shadow_addr x / 8 * 8) in *. set (hi := shadow_addr (x + n - 1) / 8 * 8 + 8) in *.
assert (Hk : (Z.to_nat (s - lo) < Z.to_nat (hi - lo))%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (lo + (s - lo)) with s in E by ring.
exact (is_someb_ok _ _ E).
Qed.

(* RPgBase.rl_cstr, conjunct by conjunct. *)
Definition cstr_chk (segs : list Segment) (h : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : bool :=
  bytes_chk (aview segs h mem) a s &&
  oz_eqb (aview segs h mem (a + Z.of_nat (length s))) 0 &&
  forallb (fun b => (0 <? b) && (b <? 256)) s &&
  (0 <? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 63) &&
  img_chk segs a (S (length s)) &&
  amem_rangeb a (Z.of_nat (length s) + 1) &&
  ra_chk (aview segs h mem) SHADOW_OFF a (S (length s)) &&
  hull_chk (aview segs h mem) a (Z.of_nat (length s) + 1).
Lemma cstr_chk_ok : forall segs h mem a s, cstr_chk segs h mem a s = true -> rl_cstr segs h mem a s.
Proof.
intros segs h mem a s Hc. unfold cstr_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9].
unfold rl_cstr.
split; [exact (bytes_chk_ok _ _ _ C1)|].
split; [exact (oz_eqb_ok _ _ C2)|].
split; [exact (bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split; [intros i Hi; apply (img_chk_ok _ _ _ C6); lia|].
split; [exact (amem_rangeb_ok _ _ C7)|].
split; [apply (ra_chk_ok _ _ _ (S (length s))); [lia | exact C8]|].
exact (hull_chk_ok _ _ _ C9).
Qed.

(* YI04.val_mem: the n little-endian bytes of v at a, read through mbyte (mem first, then the image). val_mem reads
   them with YO0f.le_byte (YI04's own import), so the checkers below name that constant. *)
Definition val_chk (segs : list Segment) (mem : word -> option byte) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (option_map (fun b : byte => bv_unsigned b) (mbyte segs mem (a + Z.of_nat k))) (YO0f.le_byte v n k))
    (seq 0 n).
Lemma val_chk_ok : forall segs mem a n v, val_chk segs mem a n v = true -> val_mem segs mem a n v.
Proof.
intros segs mem a n v Hc. unfold val_mem. intros k Hk. unfold val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E.
revert E. destruct (mbyte segs mem (a + Z.of_nat k)) as [b|]; cbn [option_map]; intros E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition cells_chk (segs : list Segment) (mem : word -> option byte) (cs : list (Z * Z)) : bool :=
  forallb (fun c => val_chk segs mem (fst c) 8 (snd c)) cs.
Lemma cells_chk_ok : forall segs mem cs, cells_chk segs mem cs = true ->
  Forall (fun c => val_mem segs mem (fst c) 8 (snd c)) cs.
Proof.
intros segs mem cs H. apply Forall_forall. intros c Hc. cbv beta. unfold cells_chk in H. rewrite forallb_forall in H.
apply val_chk_ok. exact (H c Hc).
Qed.

(* Image-only reads (seg_rom, no memory). *)
Definition img_byte (segs : list Segment) (a : Z) : option Z :=
  option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Definition img_val_chk (segs : list Segment) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (YO0f.le_byte v n k)) (seq 0 n).
Lemma img_val_chk_ok : forall segs a n v, img_val_chk segs a n v = true ->
  forall k, (k < n)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k)).
Proof.
intros segs a n v Hc k Hk. unfold img_val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E. unfold img_byte in E.
revert E. destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; cbn [option_map]; intros E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition img_bytes_chk (segs : list Segment) (a : Z) (l : list Z) : bool :=
  forallb (fun k => oz_eqb (img_byte segs (a + Z.of_nat k)) (nth k l 0)) (seq 0 (length l)).
(* (address, 4-byte word) pairs. *)
Definition entries_chk (segs : list Segment) (l : list (Z * Z)) : bool := forallb (fun e => img_val_chk segs (fst e) 4 (snd e)) l.
(* (address, 8-byte value) pairs. *)
Definition img_cells_chk (segs : list Segment) (cs : list (Z * Z)) : bool := forallb (fun c => img_val_chk segs (fst c) 8 (snd c)) cs.

(* ======================================== the measured image facts ======================================== *)
(* 1. Callee entries (address, first instruction word, little-endian 4 bytes), in this order: check_absent,
   check_role, check_malformed, check_answer, check_code, reac_role_cfg_changes, reac_role_cfg_apply_state,
   reac_role_refuse_code, pod_nearest, reac_role_prop_parse, pod_write_ent (image B calls the last out of line at
   three sites; image A inlines it). *)
Definition role_B_entries : list (Z * Z) :=
  [(0x82a80, 0xff010113); (0x82aac, 0xff010113); (0x82ad8, 0xff010113); (0x82b08, 0xff010113);
   (0x82b5c, 0xff010113); (0x83108, 0x00b54533); (0x83114, 0x00b50863); (0x8309c, 0xff010113);
   (0x82eb4, 0xfc010113); (0x83130, 0xfa010113); (0x82bac, 0xfd010113)].
Lemma role_B_entries_chk : entries_chk segsB role_B_entries = true.
Proof. vm_compute. reflexivity. Qed.

(* 2. The registered globals the witness uses: (descriptor address, (beg, size, size_with_redzone)). The descriptor
   table asan_globals is [AG_START, AG_STOP), 49 descriptors of 64 bytes (beg, size, size_with_redzone, name, module,
   has_dynamic_init, location, odr_indicator, each 8 bytes LE). The first nine are the strings of role_B_cstrs, the
   last is reac_role_refuse_code's table. *)
Definition AG_START : Z := 0x9f380.
Definition AG_STOP : Z := 0x9ffc0.
Definition role_B_globals : list (Z * (Z * Z * Z)) :=
  [(0x9fc80, (0x21480, 25, 64)); (0x9fcc0, (0x214c0, 8, 32)); (0x9fd00, (0x214e0, 5, 32));
   (0x9fd40, (0x21500, 10, 32)); (0x9fd80, (0x21540, 5, 32)); (0x9fdc0, (0x21560, 10, 32));
   (0x9fe00, (0x21580, 25, 64)); (0x9fe40, (0x215c0, 8, 32)); (0x9fe80, (0x215e0, 14, 32));
   (0x9ff80, (0x9a920, 16, 32))].
Definition global_chk (segs : list Segment) (e : Z * (Z * Z * Z)) : bool :=
  let '(d, (beg, n, r)) := e in
  (AG_START <=? d) && (d + 64 <=? AG_STOP) && ((d - AG_START) mod 64 =? 0) &&
  img_val_chk segs d 8 beg && img_val_chk segs (d + 8) 8 n && img_val_chk segs (d + 16) 8 r &&
  (beg mod 8 =? 0) && (0 <? n) && (n <=? r).
Definition globals_chk (segs : list Segment) (l : list (Z * (Z * Z * Z))) : bool := forallb (global_chk segs) l.
Lemma role_B_globals_chk : globals_chk segsB role_B_globals = true.
Proof. vm_compute. reflexivity. Qed.
(* The table is the one the runtime registers: asan.module_ctor (0x83034) loads a1 and a2 from the cells 0x9b748 and
   0x9b750 (auipc a0, 0x18 at 0x83044; auipc a2, 0x18 at 0x83048; ld a1, 0x704(a0); ld a2, 0x708(a2)) and calls
   __asan_register_elf_globals at 0x3fa9c (jal at 0x8305c); the two cells hold AG_START and AG_STOP. *)
Definition role_B_reg_words : list (Z * Z) :=
  [(0x83044, 0x00018517); (0x83048, 0x00018617); (0x8304c, 0x70453583); (0x83050, 0x70863603); (0x8305c, 0xa41bc0ef)].
Definition role_B_reg_cells : list (Z * Z) := [(0x9b748, AG_START); (0x9b750, AG_STOP)].
Lemma role_B_reg_chk :
  entries_chk segsB role_B_reg_words && img_cells_chk segsB role_B_reg_cells && (AG_STOP - AG_START =? 49 * 64) = true.
Proof. vm_compute. reflexivity. Qed.

(* 3. The strings (address, text = the RPgBase name): check_answer's la and lp, check_code's ln and lm,
   reac_role_cfg_apply_state's sa and sp', reac_role_refuse_code's c0 (= cov) and c1, and parse's akey. Each is
   followed by a NUL in the image and is the registered global of role_B_globals with beg = the address and
   size = length + 1. *)
Definition role_B_cstrs : list (Z * list Z) :=
  [(0x214c0, STR_APPLIED); (0x21480, STR_PENDING); (0x214e0, STR_NONE); (0x21500, STR_MALFORMED);
   (0x215c0, STR_APPLIED); (0x21580, STR_PENDING); (0x21540, STR_NONE); (0x21560, STR_MALFORMED);
   (0x215e0, map (fun x : byte => bv_unsigned x) Role.ROLE_KEY)].
Definition cstrs_img_chk (segs : list Segment) (gs : list (Z * (Z * Z * Z))) (l : list (Z * list Z)) : bool :=
  forallb (fun c => img_bytes_chk segs (fst c) (snd c ++ [0]) &&
    existsb (fun g => let '(_, (beg, n, _)) := g in (beg =? fst c) && (n =? Z.of_nat (length (snd c)) + 1)) gs) l.
Lemma role_B_cstrs_chk : cstrs_img_chk segsB role_B_globals role_B_cstrs = true.
Proof. vm_compute. reflexivity. Qed.

(* 4. reac_role_prop_parse's read-only doubles (0.5, -2^31, 2^31 and image B's two float-cast bounds):
   (cell, 8-byte value). *)
Definition dcs_B : list (Z * Z) :=
  [(0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10330, 0x41e0000000000000);
   (0x103f8, 0xc3e0000000000001); (0x10358, 0x43e0000000000000)].
Lemma dcs_B_chk : img_cells_chk segsB dcs_B = true.
Proof. vm_compute. reflexivity. Qed.

(* 5. reac_role_refuse_code's 16-byte table codes[] at 0x9a920: codes[0] = the address of "none", codes[1] = the
   address of "malformed"; its descriptor is 0x9ff80 (beg 0x9a920, size 16). *)
Definition role_B_tbl : list (Z * Z) := [(0x9a920, 0x21540); (0x9a928, 0x21560)].
Lemma role_B_tbl_chk :
  img_cells_chk segsB role_B_tbl &&
  existsb (fun g => let '(d, (beg, n, _)) := g in (d =? 0x9ff80) && (beg =? 0x9a920) && (n =? 16)) role_B_globals = true.
Proof. vm_compute. reflexivity. Qed.

(* ================================================ the witness ================================================ *)
(* No byte hidden. *)
Definition H_w : word -> bool := fun _ => false.
(* The shadow byte of the granule at g (g mod 8 = 0) of the global (beg, n, _), beg mod 8 = 0: 0 for a full granule,
   n mod 8 for the last partial one, 0xf9 (the runtime's global-redzone magic, PoisonRedZones) for a redzone one. *)
Definition gshadow (beg n g : Z) : Z := if g + 8 <=? beg + n then 0 else if g <? beg + n then n mod 8 else 0xf9.
(* The shadow byte of the granule at g: from the listed global whose [beg, beg + size_with_redzone) holds g, else 0. *)
Definition granule_shadow (gs : list (Z * (Z * Z * Z))) (g : Z) : Z :=
  match find (fun e => let '(_, (beg, _, r)) := e in (beg <=? g) && (g <? beg + r)) gs with
  | Some (_, (beg, n, _)) => gshadow beg n g
  | None => 0
  end.
(* The application spans whose shadow mem_w holds: the 64-byte-aligned span of the nine strings (the shadow hulls
   that rl_cstr's shadow_hull_vis reads) and the table's descriptor span. *)
Definition shadow_spans : list (Z * Z) := [(0x21480, 0x21600); (0x9a920, 0x9a940)].
(* mem_w holds only shadow bytes: at SHADOW_OFF + x / 8 for x in a span, the byte granule_shadow gives for x's
   granule, which is what the runtime writes when it registers the globals of role_B_globals. The only part of a
   span that no listed global covers, [0x21520, 0x21540) (after .str.37's redzone, before the next unit's .str),
   the runtime never writes: its four shadow bytes keep the 0 of the freshly mapped shadow (rl_cstr's hull for
   "malformed" at 0x21500 reads them). Every other address reads None, so each program byte (string, constant,
   table) comes from the image through mbyte's fall-back to seg_rom. *)
Definition mem_w : word -> option byte := fun w =>
  if existsb (fun r => (SHADOW_OFF + fst r / 8 <=? bv_unsigned w) && (bv_unsigned w <? SHADOW_OFF + snd r / 8)) shadow_spans
  then Some (Z_to_bv 8 (granule_shadow role_B_globals ((bv_unsigned w - SHADOW_OFF) * 8)))
  else None.

(* W1. Every string of role_B_cstrs satisfies rl_cstr at (H_w, mem_w). *)
Definition cstrs_wit_chk (l : list (Z * list Z)) : bool := forallb (fun c => cstr_chk segsB H_w mem_w (fst c) (snd c)) l.
Lemma rl_cstr_B_chk : cstrs_wit_chk role_B_cstrs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rl_cstr_B : forall a s, In (a, s) role_B_cstrs -> rl_cstr segsB H_w mem_w a s.
Proof.
intros a s Hin. apply cstr_chk_ok.
pose proof rl_cstr_B_chk as E. unfold cstrs_wit_chk in E. rewrite forallb_forall in E.
exact (E (a, s) Hin).
Qed.
Print Assumptions rl_cstr_B.
(* A control: without the shadow bytes the checker refuses the first string (its shadow reads None). *)
Lemma rl_cstr_B_control : cstr_chk segsB H_w (fun _ => None) 0x214c0 STR_APPLIED = false.
Proof. vm_compute. reflexivity. Qed.

(* W2. parse's read-only doubles. *)
Lemma rl_ro_cells_B : rl_ro_cells segsB H_w mem_w dcs_B.
Proof. unfold rl_ro_cells. apply cells_chk_ok. vm_compute. reflexivity. Qed.
Print Assumptions rl_ro_cells_B.

(* W3. reac_role_refuse_code's table premises at tbl = 0x9a920, c0 = 0x21540, c1 = 0x21560. *)
Lemma rl_refuse_tbl_B :
  val_mem segsB (mrestrict H_w mem_w) 0x9a920 8 0x21540 /\
  val_mem segsB (mrestrict H_w mem_w) (0x9a920 + 8) 8 0x21560 /\
  range_addressable (aview segsB H_w mem_w) SHADOW_OFF 0x9a920 16 /\
  (forall i, 0 <= i < 16 -> in_img segsB (0x9a920 + i)).
Proof.
split; [apply val_chk_ok; vm_compute; reflexivity|].
split; [apply val_chk_ok; vm_compute; reflexivity|].
split; [apply (ra_chk_ok _ _ _ 16); [reflexivity | vm_compute; reflexivity]|].
intros i Hi. apply (img_chk_ok segsB 0x9a920 16); [vm_compute; reflexivity | exact Hi].
Qed.
Print Assumptions rl_refuse_tbl_B.

(* W4. Each callee entry holds its measured first instruction word in the image. *)
Lemma rl_entries_B : forall a w, In (a, w) role_B_entries ->
  forall k, (k < 4)%nat -> seg_rom segsB (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (img_val_chk_ok segsB a 4 w _ k Hk).
pose proof role_B_entries_chk as E. unfold entries_chk in E. rewrite forallb_forall in E.
exact (E (a, w) Hin).
Qed.
Print Assumptions rl_entries_B.

(* W5. The string premises of rl_check_answer_specX at (la, lp) = (0x214c0, 0x21480), with s = 0x215c0 ("applied")
   when cur = req and s = 0x21580 ("role_reestablish_pending") otherwise, and of rl_check_code_specX at
   (ln, lm) = (0x214e0, 0x21500) with (sn, sm) = (0x21540, 0x21560), in the order the contracts state them. *)
Lemma rl_cstr_B_at : forall n a s, nth_error role_B_cstrs n = Some (a, s) -> rl_cstr segsB H_w mem_w a s.
Proof. intros n a s E. apply rl_cstr_B. eapply nth_error_In. exact E. Qed.
Lemma rl_sat_cmp_B :
  (forall cur req : Z,
    rl_cstr segsB H_w mem_w (if cur =? req then 0x215c0 else 0x21580) (if cur =? req then STR_APPLIED else STR_PENDING) /\
    rl_cstr segsB H_w mem_w 0x214c0 STR_APPLIED /\ rl_cstr segsB H_w mem_w 0x21480 STR_PENDING) /\
  (rl_cstr segsB H_w mem_w 0x21540 STR_NONE /\ rl_cstr segsB H_w mem_w 0x21560 STR_MALFORMED /\
   rl_cstr segsB H_w mem_w 0x214e0 STR_NONE /\ rl_cstr segsB H_w mem_w 0x21500 STR_MALFORMED).
Proof.
split.
- intros cur req. split; [|split].
  + destruct (cur =? req); [apply (rl_cstr_B_at 4) | apply (rl_cstr_B_at 5)]; reflexivity.
  + apply (rl_cstr_B_at 0); reflexivity.
  + apply (rl_cstr_B_at 1); reflexivity.
- split; [|split; [|split]].
  + apply (rl_cstr_B_at 6); reflexivity.
  + apply (rl_cstr_B_at 7); reflexivity.
  + apply (rl_cstr_B_at 2); reflexivity.
  + apply (rl_cstr_B_at 3); reflexivity.
Qed.
Print Assumptions rl_sat_cmp_B.
