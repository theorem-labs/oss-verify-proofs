(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Class annOV := mkAnnOV {
  ann_ov : aptr -> option (list byte);
  ann_ovs : Z -> option (list byte)
}.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition AMAGIC : Z := 0xCC6E96B9CC6E96B9.
Definition ARI_STRIDE : Z := 128.
Definition ASTATS_WORDS : nat := 46%nat.

Inductive bstate :=
| BLive (p : aptr)
| BQuar
| BBatch.

Record xbusy := mkXBusy {
  xb_class : Z;
  xb_slot : Z;
  xb_n : Z;
  xb_st : bstate;
  xb_b1 : Z;
  xb_ctx : Z
}.

Record xclass := mkXClass {
  xc_free : list Z;
  xc_cache : list Z
}.

Record aconc := mkAConc {
  x_cls : Z -> xclass;
  x_busy : list xbusy
}.

Definition aregion (L : alayout) (c : Z) : Z := al_space_beg L + c * K_REGION.
Definition aslot_addr (L : alayout) (c k : Z) : Z := aregion L c + k * size_of_class c.
Definition afreearr (L : alayout) (c : Z) : Z := aregion L c + K_FREEARR_OFF.
Definition aregion_info (L : alayout) (c : Z) : Z := al_space_beg L + K_SPACE_SIZE + c * ARI_STRIDE.
Definition acompact (c k : Z) : Z := k * (size_of_class c / 16).

Definition xb_alloc (L : alayout) (b : xbusy) : Z := aslot_addr L (xb_class b) (xb_slot b).
Definition xb_user (L : alayout) (b : xbusy) : Z := xb_alloc L b + rz_size (xb_n b).
Definition xb_hdr (L : alayout) (b : xbusy) : Z := xb_user L b - 16.

Definition ndist (st : astate) (c : Z) : Z := c_allocated_user (get_cls st c) / size_of_class c.

Definition busy_of (X : aconc) (c k : Z) : option xbusy :=
  List.find (fun b => (xb_class b =? c) && (xb_slot b =? k)) (x_busy X).
Definition busy_slots (X : aconc) (c : Z) : list Z :=
  List.map xb_slot (List.filter (fun b => xb_class b =? c) (x_busy X)).

Definition junk_at (m : amem) (A len : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat len) bs].

Definition fill_at (m : amem) (A len v : Z) : Prop :=
  rw_cells asegs m A [CB (Z.to_nat len) (repeat (Z_to_bv 8 v) (Z.to_nat len))].

Definition arep_rt (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560)]
  /\ rw_cells asegs m 0xd1508 [C8 (Z_to_bv 64 0x16b5e8); C8 (Z_to_bv 64 0xd72b8); C8 (Z_to_bv 64 0xd9ab8);
                                C8 (Z_to_bv 64 0xda7a8); C8 (Z_to_bv 64 0xda7b0); C8 (Z_to_bv 64 0xda7a0)]
  /\ rw_cells asegs m 0xd1538 [C8 (Z_to_bv 64 0xd3428)]
  /\ rw_cells asegs m 0xd2080 [C8 (Z_to_bv 64 0xda799)]
  /\ rw_cells asegs m 0xd2170 [C8 (Z_to_bv 64 0x10)]
  /\ rw_cells asegs m 0xd3420 [C8 (Z_to_bv 64 0xc74a0); C8 (Z_to_bv 64 0xc78a4)]
  /\ rw_cells asegs m 0xd7278 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)]

  /\ rw_cells asegs m 0xd72b8 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)]

  /\ rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]
  /\ rw_cells asegs m 0xd730d [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd9ab8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xd931c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xd9320 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xd9324 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xda798 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0xda7a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xda7bc [C4 (Z_to_bv 64 30)]
  /\ (exists oomb : byte, rw_cells asegs m 0x15bd20 [C1 oomb; C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)])
  /\ rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x16b580 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0x16b608 [C8 (Z_to_bv 64 0x1e00010000)]
  /\ rw_cells asegs m 0x16b60a [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x16b660 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m 0x60cc90 [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))].

Definition ainstance (L : alayout) (st : astate) (m : amem) : Prop :=
     rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 (al_space_beg L))]
  /\ rw_cells asegs m (AINSTANCE + 48) [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]
  /\ rw_cells asegs m (AINSTANCE + 64) [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m (AINSTANCE + 72) [C8 (Z_to_bv 64 (al_ptr_array L))]
  /\ rw_cells asegs m (AINSTANCE + 112) [C8 (Z_to_bv 64 (a_nres st)); C8 (Z_to_bv 64 (a_nsec st))]
  /\ rw_cells asegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m (AINSTANCE + 984) [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m (AINSTANCE + 40) [C4 (Z_to_bv 64 4294967295)]
  /\ rw_cells asegs m (AINSTANCE + 56) [C1 (Z_to_bv 8 0)].

Definition acache_addr (L : alayout) (c : Z) : Z := al_t L + 208 + c * 80.
Definition acache_cells (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let xc := x_cls X c in
  exists tail : list word,
     rw_cells asegs m (acache_addr L c)
       [C4 (Z_to_bv 64 (c_count (get_cls st c))); C4 (Z_to_bv 64 (max_count st c));
        C8 (Z_to_bv 64 (if a_cinit st then size_of_class c else 0))]
  /\ u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache xc) ++ tail)
  /\ (length (xc_cache xc) + length tail = 16)%nat.

Definition athread (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     rw_cells asegs m (al_t L) [C8 (Z_to_bv 64 (al_ctx L)); C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))]
  /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st X m c)
  /\ junk_at m (al_t L + 2768) 32
  /\ (exists sj, u64arr asegs m (al_t L + 2800) sj /\ length sj = ASTATS_WORDS)
  /\ rw_cells asegs m (al_t L + 3168) [C1 (Z_to_bv 8 0)].

Definition aflag_cell (L : alayout) (m : amem) (c : Z) : Prop :=
  if c =? K_BATCH_CLASS then rw_cells asegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 0)] else junk_at m (aregion_info L c + 68) 1.
Definition aregion_cells (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     rw_cells asegs m (aregion_info L c) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 (c_mapped_free_array r));
        C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0)  ;
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)  ]
  /\ junk_at m (aregion_info L c + 64) 4
  /\ aflag_cell L m c
  /\ junk_at m (aregion_info L c + 72) 56.

Definition afreearray (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let xc := x_cls X c in
     u32arr asegs m (afreearr L c) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free xc))
  /\ junk_at m (afreearr L c + 4 * c_num_freed r) (c_mapped_free_array r - 4 * c_num_freed r)
  /\ junk_at m (shad (afreearr L c)) (shlen (c_mapped_free_array r)).

Definition bstate_byte (s : bstate) : option Z :=
  match s with BLive _ => Some 2 | BQuar => Some 3 | BBatch => None end.

Definition aslot_busy (L : alayout) (m : amem) (b : xbusy) : Prop :=
  let c := xb_class b in let S := size_of_class c in
  let AB := xb_alloc L b in let n := xb_n b in let rz := rz_size n in let UB := AB + rz in let HB := UB - 16 in
  match xb_st b with
  | BBatch => junk_at m AB S
  | s =>
       (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 HB)] /\ junk_at m (AB + 16) (rz - 32))
    /\ (exists stb, bstate_byte s = Some stb /\
           rw_cells asegs m HB [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 (xb_b1 b)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (xb_ctx b))])
    /\ junk_at m UB (S - rz)
  end.

Definition aslots (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        match busy_of X c k with
        | None => junk_at m (aslot_addr L c k) S
        | Some b => aslot_busy L m b
        end)
  /\ junk_at m (aregion L c + c_allocated_user r) (c_mapped_user r - c_allocated_user r).

Definition granules (n : Z) : Z := shlen (n + 7).
Definition block_shadow_bytes (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (shlen n)) ++
  (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).

Definition live_bytes (p : aptr) (n : Z) : list byte :=
  match ann_ov p with
  | Some bs => if Nat.eqb (length bs) (Z.to_nat (granules n)) then bs else block_shadow_bytes n
  | None => block_shadow_bytes n
  end.
Lemma live_bytes_none : forall p n, ann_ov p = None -> live_bytes p n = block_shadow_bytes n.
Proof. intros p n E. unfold live_bytes. rewrite E. reflexivity. Qed.
Definition slot_shadow_bytes (S : Z) (b : option xbusy) : list byte :=
  match b with
  | None => repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S))
  | Some b =>
      let n := xb_n b in let rz := rz_size n in
      let mid := match xb_st b with
                 | BLive p => live_bytes p n
                 | BQuar => repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))
                 | BBatch => repeat (Z_to_bv 8 0xfa) (Z.to_nat (granules n))
                 end in
      repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)) ++ mid
      ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n))
  end.
Definition aslot_shadow (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        rw_cells asegs m (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen S)) (slot_shadow_bytes S (busy_of X c k))])
  /\ fill_at m (shad (aregion L c + c_allocated_user r)) (shlen (c_mapped_user r - c_allocated_user r)) 0xfa.

Definition awf (L : alayout) (st : astate) (X : aconc) : Prop :=
     a_space_beg st = al_space_beg L /\ a_ptr_array st = al_ptr_array L
  /\ al_space_beg L mod K_ALIGN = 0 /\ 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP

  /\ (forall c, 1 <= c < K_NUM_CLASSES ->
        let r := get_cls st c in let xc := x_cls X c in let S := size_of_class c in
           0 <= c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
        /\ c_allocated_user r mod S = 0 /\ c_mapped_user r mod K_USER_MAP = 0
        /\ 0 <= c_num_freed r /\ 4 * c_num_freed r <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
        /\ Z.of_nat (length (xc_free xc)) = c_num_freed r
        /\ Z.of_nat (length (xc_cache xc)) = c_count r /\ 0 <= c_count r <= max_count st c
        /\ List.NoDup (xc_free xc ++ xc_cache xc ++ busy_slots X c)
        /\ (forall k, In k (xc_free xc ++ xc_cache xc ++ busy_slots X c) -> 0 <= k < ndist st c))

  /\ (forall c, ~ (1 <= c < K_NUM_CLASSES) -> get_cls st c = aclass0)

  /\ (forall b, In b (x_busy X) ->
        1 <= xb_class b < K_NUM_CLASSES
        /\ match xb_st b with
           | BLive p => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1
                        /\ 0 <= xb_ctx b < 2^31
                        /\ (a_live st) !! p = Some (CPrim (xb_class b) (xb_n b))
           | BQuar => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 /\ 0 <= xb_ctx b < 2^31
           | BBatch => xb_class b = K_BATCH_CLASS
           end)
  /\ (forall p c n, (a_live st) !! p = Some (CPrim c n) -> exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_class b = c /\ xb_n b = n)
  /\ (forall p ch, (a_live st) !! p = Some ch -> (p < a_next st)%N)
  /\ (forall b1 b2, In b1 (x_busy X) -> In b2 (x_busy X) -> xb_st b1 = xb_st b2 -> (exists p, xb_st b1 = BLive p) -> b1 = b2).

Record aholes := mkAHoles {
  ah_quar : alayout -> astate -> aconc -> amem -> Prop;
  ah_sec : alayout -> astate -> aconc -> amem -> Prop;
  ah_depot : alayout -> amem -> Prop;
  ah_fake : alayout -> list ablock -> amem -> Prop
}.

Definition arelro (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

Definition azero (m : amem) (A n : Z) : Prop :=
  (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at asegs m A n.
Definition ashadow_avail (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     azero m (shad (aregion L c + c_mapped_user r)) (shlen (K_FREEARR_OFF - c_mapped_user r))
  /\ azero m (shad (afreearr L c + c_mapped_free_array r)) (shlen (K_FREEARR_MAX - c_mapped_free_array r)).

Definition arep_rt2 (m : amem) : Prop :=
     rw_cells asegs m 0x16b6ec [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x16b678 [C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xd33b0 [C8 (Z_to_bv 64 0xc2aa0)].

Definition arep_rt3 (m : amem) : Prop :=
     rw_cells asegs m 0xd3310 [C8 (Z_to_bv 64 0xc6dec); C8 (Z_to_bv 64 0xc3cdc)]
  /\ rw_cells asegs m 0xd32f0 [C8 (Z_to_bv 64 0xccba4)]
  /\ rw_cells asegs m 0xd32f8 [C8 (Z_to_bv 64 0xc3aa8)]
  /\ rw_cells asegs m 0xd33d0 [C8 (Z_to_bv 64 0xc7d2c)]
  /\ rw_cells asegs m 0xd32e0 [C8 (Z_to_bv 64 0xc73a4)]
  /\ rw_cells asegs m 0x16b638 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells asegs m 0x16b6e0 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells asegs m 0xd9ac0 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xd7318 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x169558 [C4 (Z_to_bv 64 0)]

  /\ rw_cells asegs m 0xd14f8 [C8 (Z_to_bv 64 0x169560); C8 (Z_to_bv 64 0xd3460)]
  /\ rw_cells asegs m 0xd3460 [C8 (Z_to_bv 64 0x1a484)]
  /\ rw_cells asegs m 0x169560 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x16b6c0 [C8 (Z_to_bv 64 0x10101000100)]
  /\ rw_cells asegs m 0x16b6d8 [C8 (Z_to_bv 64 0x101000100000000)]
  /\ (exists cb : list byte, rw_cells asegs m 0x62ccc0 [CB 8 cb])
  /\ rw_cells asegs m 0x62cf40 [C8 (Z_to_bv 64 4096)].

Definition AREP (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_sec H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.

Section KitStatements.
Variable H : aholes.

Definition kit_cache_pop_stmt : Prop :=
  forall L st X m c cnt, AREP H L st X m -> 1 <= c < K_NUM_CLASSES ->
  c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k
    /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (acache_addr L c)
         [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (acache_addr L c + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k))
    /\ junk_at m (aslot_addr L c k) (size_of_class c)
    /\ fill_at m (shad (aslot_addr L c k)) (shlen (size_of_class c)) 0xfa.

Definition kit_malloc_fast_stmt : Prop :=
  forall L st X m m' c k n (p : aptr) b1 ctx,
  AREP H L st X m -> 1 <= c < K_NUM_CLASSES -> is_primary n = true -> class_id (needed_size n) = c ->
  0 < c_count (get_cls st c) ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (c_count (get_cls st c) - 1)) = Some k ->
  (a_live st) !! p = None -> 0 <= b1 < 0x80 -> 0 <= ctx < 2^31 ->
  let b := mkXBusy c k n (BLive p) b1 ctx in
  let st' := set_next (N.succ (a_next st)) (set_live (<[p := CPrim c n]> (a_live st))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)) in

  (m' = m -> False) ->
  AREP H L st' (mkAConc (x_cls X) (b :: x_busy X)) m'.

Definition hole_frame_stmt (P : alayout -> amem -> Prop) (FP : alayout -> Z -> Prop) : Prop :=
  forall L m m' (W : list (Z * Z)),
    P L m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv -> ~ FP L a) W -> P L m'.
End KitStatements.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Class annOV := mkAnnOV {
  ann_ov : aptr -> option (list byte);
  ann_ovs : Z -> option (list byte)
}.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition AMAGIC : Z := 0xCC6E96B9CC6E96B9.
Definition ARI_STRIDE : Z := 128.
Definition ASTATS_WORDS : nat := 46%nat.

Inductive bstate :=
| BLive (p : aptr)
| BQuar
| BBatch.

Record xbusy := mkXBusy {
  xb_class : Z;
  xb_slot : Z;
  xb_n : Z;
  xb_st : bstate;
  xb_b1 : Z;
  xb_ctx : Z
}.

Record xclass := mkXClass {
  xc_free : list Z;
  xc_cache : list Z
}.

Record aconc := mkAConc {
  x_cls : Z -> xclass;
  x_busy : list xbusy
}.

Definition aregion (L : alayout) (c : Z) : Z := al_space_beg L + c * K_REGION.
Definition aslot_addr (L : alayout) (c k : Z) : Z := aregion L c + k * size_of_class c.
Definition afreearr (L : alayout) (c : Z) : Z := aregion L c + K_FREEARR_OFF.
Definition aregion_info (L : alayout) (c : Z) : Z := al_space_beg L + K_SPACE_SIZE + c * ARI_STRIDE.
Definition acompact (c k : Z) : Z := k * (size_of_class c / 16).

Definition xb_alloc (L : alayout) (b : xbusy) : Z := aslot_addr L (xb_class b) (xb_slot b).
Definition xb_user (L : alayout) (b : xbusy) : Z := xb_alloc L b + rz_size (xb_n b).
Definition xb_hdr (L : alayout) (b : xbusy) : Z := xb_user L b - 16.

Definition ndist (st : astate) (c : Z) : Z := c_allocated_user (get_cls st c) / size_of_class c.

Definition busy_of (X : aconc) (c k : Z) : option xbusy :=
  List.find (fun b => (xb_class b =? c) && (xb_slot b =? k)) (x_busy X).
Definition busy_slots (X : aconc) (c : Z) : list Z :=
  List.map xb_slot (List.filter (fun b => xb_class b =? c) (x_busy X)).

Definition junk_at (m : amem) (A len : Z) : Prop :=
  exists bs, rw_cells bsegs m A [CB (Z.to_nat len) bs].

Definition fill_at (m : amem) (A len v : Z) : Prop :=
  rw_cells bsegs m A [CB (Z.to_nat len) (repeat (Z_to_bv 8 v) (Z.to_nat len))].

Definition arep_rt (L : alayout) (m : amem) : Prop :=
     rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720)]
  /\ rw_cells bsegs m 0xd3620 [C8 (Z_to_bv 64 0x16d7a8); C8 (Z_to_bv 64 0xd9478); C8 (Z_to_bv 64 0xdbc78);
                                C8 (Z_to_bv 64 0xdc968); C8 (Z_to_bv 64 0xdc970); C8 (Z_to_bv 64 0xdc960)]
  /\ rw_cells bsegs m 0xd3650 [C8 (Z_to_bv 64 0xd5540)]
  /\ rw_cells bsegs m 0xd4198 [C8 (Z_to_bv 64 0xdc959)]
  /\ rw_cells bsegs m 0xd4288 [C8 (Z_to_bv 64 0x10)]
  /\ rw_cells bsegs m 0xd5538 [C8 (Z_to_bv 64 0xc95bc); C8 (Z_to_bv 64 0xc99c0)]
  /\ rw_cells bsegs m 0xd9438 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)]

  /\ rw_cells bsegs m 0xd9478 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)]

  /\ rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]
  /\ rw_cells bsegs m 0xd94cd [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xdbc78 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells bsegs m 0xdb4dc [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xdb4e0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xdb4e4 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xdc958 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xdc960 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xdc97c [C4 (Z_to_bv 64 30)]
  /\ (exists oomb : byte, rw_cells bsegs m 0x15dee0 [C1 oomb; C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)])
  /\ rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x16d740 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0x16d7c8 [C8 (Z_to_bv 64 0x1e00010000)]
  /\ rw_cells bsegs m 0x16d7ca [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x16d820 [C8 (Z_to_bv 64 0xffffffffffffffff)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m 0x60ee50 [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))].

Definition ainstance (L : alayout) (st : astate) (m : amem) : Prop :=
     rw_cells bsegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 (al_space_beg L))]
  /\ rw_cells bsegs m (AINSTANCE + 48) [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]
  /\ rw_cells bsegs m (AINSTANCE + 64) [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m (AINSTANCE + 72) [C8 (Z_to_bv 64 (al_ptr_array L))]
  /\ rw_cells bsegs m (AINSTANCE + 112) [C8 (Z_to_bv 64 (a_nres st)); C8 (Z_to_bv 64 (a_nsec st))]
  /\ rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (AINSTANCE + 984) [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m (AINSTANCE + 40) [C4 (Z_to_bv 64 4294967295)]
  /\ rw_cells bsegs m (AINSTANCE + 56) [C1 (Z_to_bv 8 0)].

Definition acache_addr (L : alayout) (c : Z) : Z := al_t L + 208 + c * 80.
Definition acache_cells (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let xc := x_cls X c in
  exists tail : list word,
     rw_cells bsegs m (acache_addr L c)
       [C4 (Z_to_bv 64 (c_count (get_cls st c))); C4 (Z_to_bv 64 (max_count st c));
        C8 (Z_to_bv 64 (if a_cinit st then size_of_class c else 0))]
  /\ u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache xc) ++ tail)
  /\ (length (xc_cache xc) + length tail = 16)%nat.

Definition athread (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     rw_cells bsegs m (al_t L) [C8 (Z_to_bv 64 (al_ctx L)); C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))]
  /\ rw_cells bsegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st X m c)
  /\ junk_at m (al_t L + 2768) 32
  /\ (exists sj, u64arr bsegs m (al_t L + 2800) sj /\ length sj = ASTATS_WORDS)
  /\ rw_cells bsegs m (al_t L + 3168) [C1 (Z_to_bv 8 0)].

Definition aflag_cell (L : alayout) (m : amem) (c : Z) : Prop :=
  if c =? K_BATCH_CLASS then rw_cells bsegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 0)] else junk_at m (aregion_info L c + 68) 1.
Definition aregion_cells (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     rw_cells bsegs m (aregion_info L c) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 (c_mapped_free_array r));
        C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0)  ;
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)  ]
  /\ junk_at m (aregion_info L c + 64) 4
  /\ aflag_cell L m c
  /\ junk_at m (aregion_info L c + 72) 56.

Definition afreearray (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let xc := x_cls X c in
     u32arr bsegs m (afreearr L c) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free xc))
  /\ junk_at m (afreearr L c + 4 * c_num_freed r) (c_mapped_free_array r - 4 * c_num_freed r)
  /\ junk_at m (shad (afreearr L c)) (shlen (c_mapped_free_array r)).

Definition bstate_byte (s : bstate) : option Z :=
  match s with BLive _ => Some 2 | BQuar => Some 3 | BBatch => None end.

Definition aslot_busy (L : alayout) (m : amem) (b : xbusy) : Prop :=
  let c := xb_class b in let S := size_of_class c in
  let AB := xb_alloc L b in let n := xb_n b in let rz := rz_size n in let UB := AB + rz in let HB := UB - 16 in
  match xb_st b with
  | BBatch => junk_at m AB S
  | s =>
       (16 < rz -> rw_cells bsegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 HB)] /\ junk_at m (AB + 16) (rz - 32))
    /\ (exists stb, bstate_byte s = Some stb /\
           rw_cells bsegs m HB [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 (xb_b1 b)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (xb_ctx b))])
    /\ junk_at m UB (S - rz)
  end.

Definition aslots (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        match busy_of X c k with
        | None => junk_at m (aslot_addr L c k) S
        | Some b => aslot_busy L m b
        end)
  /\ junk_at m (aregion L c + c_allocated_user r) (c_mapped_user r - c_allocated_user r).

Definition granules (n : Z) : Z := shlen (n + 7).
Definition block_shadow_bytes (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (shlen n)) ++
  (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).

Definition live_bytes (p : aptr) (n : Z) : list byte :=
  match ann_ov p with
  | Some bs => if Nat.eqb (length bs) (Z.to_nat (granules n)) then bs else block_shadow_bytes n
  | None => block_shadow_bytes n
  end.
Lemma live_bytes_none : forall p n, ann_ov p = None -> live_bytes p n = block_shadow_bytes n.
Proof. intros p n E. unfold live_bytes. rewrite E. reflexivity. Qed.
Definition slot_shadow_bytes (S : Z) (b : option xbusy) : list byte :=
  match b with
  | None => repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S))
  | Some b =>
      let n := xb_n b in let rz := rz_size n in
      let mid := match xb_st b with
                 | BLive p => live_bytes p n
                 | BQuar => repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))
                 | BBatch => repeat (Z_to_bv 8 0xfa) (Z.to_nat (granules n))
                 end in
      repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)) ++ mid
      ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n))
  end.
Definition aslot_shadow (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        rw_cells bsegs m (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen S)) (slot_shadow_bytes S (busy_of X c k))])
  /\ fill_at m (shad (aregion L c + c_allocated_user r)) (shlen (c_mapped_user r - c_allocated_user r)) 0xfa.

Definition awf (L : alayout) (st : astate) (X : aconc) : Prop :=
     a_space_beg st = al_space_beg L /\ a_ptr_array st = al_ptr_array L
  /\ al_space_beg L mod K_ALIGN = 0 /\ 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP

  /\ (forall c, 1 <= c < K_NUM_CLASSES ->
        let r := get_cls st c in let xc := x_cls X c in let S := size_of_class c in
           0 <= c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
        /\ c_allocated_user r mod S = 0 /\ c_mapped_user r mod K_USER_MAP = 0
        /\ 0 <= c_num_freed r /\ 4 * c_num_freed r <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
        /\ Z.of_nat (length (xc_free xc)) = c_num_freed r
        /\ Z.of_nat (length (xc_cache xc)) = c_count r /\ 0 <= c_count r <= max_count st c
        /\ List.NoDup (xc_free xc ++ xc_cache xc ++ busy_slots X c)
        /\ (forall k, In k (xc_free xc ++ xc_cache xc ++ busy_slots X c) -> 0 <= k < ndist st c))

  /\ (forall c, ~ (1 <= c < K_NUM_CLASSES) -> get_cls st c = aclass0)

  /\ (forall b, In b (x_busy X) ->
        1 <= xb_class b < K_NUM_CLASSES
        /\ match xb_st b with
           | BLive p => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1
                        /\ 0 <= xb_ctx b < 2^31
                        /\ (a_live st) !! p = Some (CPrim (xb_class b) (xb_n b))
           | BQuar => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 /\ 0 <= xb_ctx b < 2^31
           | BBatch => xb_class b = K_BATCH_CLASS
           end)
  /\ (forall p c n, (a_live st) !! p = Some (CPrim c n) -> exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_class b = c /\ xb_n b = n)
  /\ (forall p ch, (a_live st) !! p = Some ch -> (p < a_next st)%N)
  /\ (forall b1 b2, In b1 (x_busy X) -> In b2 (x_busy X) -> xb_st b1 = xb_st b2 -> (exists p, xb_st b1 = BLive p) -> b1 = b2).

Record aholes := mkAHoles {
  ah_quar : alayout -> astate -> aconc -> amem -> Prop;
  ah_sec : alayout -> astate -> aconc -> amem -> Prop;
  ah_depot : alayout -> amem -> Prop;
  ah_fake : alayout -> list ablock -> amem -> Prop
}.

Definition arelro (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

Definition azero (m : amem) (A n : Z) : Prop :=
  (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at bsegs m A n.
Definition ashadow_avail (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     azero m (shad (aregion L c + c_mapped_user r)) (shlen (K_FREEARR_OFF - c_mapped_user r))
  /\ azero m (shad (afreearr L c + c_mapped_free_array r)) (shlen (K_FREEARR_MAX - c_mapped_free_array r)).

Definition arep_rt2 (m : amem) : Prop :=
     rw_cells bsegs m 0x16d8ac [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x16d838 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xd54c8 [C8 (Z_to_bv 64 0xc4bbc)].

Definition arep_rt3 (m : amem) : Prop :=
     rw_cells bsegs m 0xd5428 [C8 (Z_to_bv 64 0xc8f08); C8 (Z_to_bv 64 0xc5df8)]
  /\ rw_cells bsegs m 0xd5408 [C8 (Z_to_bv 64 0xcecc0)]
  /\ rw_cells bsegs m 0xd5410 [C8 (Z_to_bv 64 0xc5bc4)]
  /\ rw_cells bsegs m 0xd54e8 [C8 (Z_to_bv 64 0xc9e48)]
  /\ rw_cells bsegs m 0xd53f8 [C8 (Z_to_bv 64 0xc94c0)]
  /\ rw_cells bsegs m 0x16d7f8 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells bsegs m 0x16d8a0 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells bsegs m 0xdbc80 [C4 (Z_to_bv 64 1)]
  /\ rw_cells bsegs m 0xd94d8 [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0x16b718 [C4 (Z_to_bv 64 0)]

  /\ rw_cells bsegs m 0xd3610 [C8 (Z_to_bv 64 0x16b720); C8 (Z_to_bv 64 0xd5578)]
  /\ rw_cells bsegs m 0xd5578 [C8 (Z_to_bv 64 0x1a442)]
  /\ rw_cells bsegs m 0x16b720 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells bsegs m 0x16d880 [C8 (Z_to_bv 64 0x10101000100)]
  /\ rw_cells bsegs m 0x16d898 [C8 (Z_to_bv 64 0x101000100000000)]
  /\ (exists cb : list byte, rw_cells bsegs m 0x62ee80 [CB 8 cb])
  /\ rw_cells bsegs m 0x62f100 [C8 (Z_to_bv 64 4096)].

Definition AREP (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_sec H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.

Section KitStatements.
Variable H : aholes.

Definition kit_cache_pop_stmt : Prop :=
  forall L st X m c cnt, AREP H L st X m -> 1 <= c < K_NUM_CLASSES ->
  c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k
    /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells bsegs m (acache_addr L c)
         [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr bsegs m (acache_addr L c + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k))
    /\ junk_at m (aslot_addr L c k) (size_of_class c)
    /\ fill_at m (shad (aslot_addr L c k)) (shlen (size_of_class c)) 0xfa.

Definition kit_malloc_fast_stmt : Prop :=
  forall L st X m m' c k n (p : aptr) b1 ctx,
  AREP H L st X m -> 1 <= c < K_NUM_CLASSES -> is_primary n = true -> class_id (needed_size n) = c ->
  0 < c_count (get_cls st c) ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (c_count (get_cls st c) - 1)) = Some k ->
  (a_live st) !! p = None -> 0 <= b1 < 0x80 -> 0 <= ctx < 2^31 ->
  let b := mkXBusy c k n (BLive p) b1 ctx in
  let st' := set_next (N.succ (a_next st)) (set_live (<[p := CPrim c n]> (a_live st))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)) in

  (m' = m -> False) ->
  AREP H L st' (mkAConc (x_cls X) (b :: x_busy X)) m'.

Definition hole_frame_stmt (P : alayout -> amem -> Prop) (FP : alayout -> Z -> Prop) : Prop :=
  forall L m m' (W : list (Z * Z)),
    P L m -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv -> ~ FP L a) W -> P L m'.
End KitStatements.
End CANSEC1.

End TwinB.
