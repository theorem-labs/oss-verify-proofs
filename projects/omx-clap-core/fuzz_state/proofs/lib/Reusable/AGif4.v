(* copied from proofs/cgif/cgif_file_fuzzer/lib/AGif4.v @ 84ee52cd012 (c5 of record, installed 20:18Z: CZS hole INSTv + 400 -> + 408), module paths changed only. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* The interface between the SECONDARY path of the frame-generic Allocate walk (n >= 64513, the
   LargeMmapAllocator) and an allocator model.  It is the secondary twin of AGif0n.AIface: the hit-g arm reads the
   machine through AIface's fields, the secondary arm reads it through AIfaceS's.

   The walk's own files (AGjw / AGjx and the segment files AGjh..AGju) read the machine only through
   the VIEW AGif2.sview.  What is left, and what this interface names, is:
   - (a) [ifs_view]: the pre-state's cells are that view, with the model's counters (the live secondary chunks and
     the reserved pointer-array slots);
   - (b) [ifs_shape]: at a secondary size the model tree is the tick, the size check and [sec_alloc];
   - (c) the kernel: the walk asks the kernel twice (mmap for the block, and mmap for the next pointer-array
     commit when the array is full).  [ifs_mwf], [ifs_room], [ifs_ledger] are what the node needs of the model,
     [ifs_grant] that a grant exists at all, [ifs_apart] what the granted address is worth (its zone, that it is
     apart from everything the allocator already owns, and that its shadow is zero);
   - (d) the post: [ifs_post_null] (the refusal: the result is PNull and the out-of-memory byte is set) and
     [ifs_post_grant] (the grant: the new block, the grown layout and the new state).

   The machine post at Allocate's ret is the record [sfin] below; the kernel's effect on the world and the model
   is [skern].  Both are stated over the instance [inst] (never over cgif's TFIB_INST) and over the abstract
   depot post [dpost] of AGif0n, so that a second instance (the shared preset/reply instance) can discharge them.

   The file is image-free: the binary's segments and data cells are the fields of the class ImgBase.AImg, and the
   shadow offset, the image addresses of the const zone [CZS], the depot's write zone, StackDepotPut's entry pc,
   the grant zones and the walk's frame at Allocate's entry are the fields of ImgBaseAGS.AImgS ([Context {IM : AImg}
   {IMS : AImgS}]).  The geometry of the secondary block (AGjm's), the stack sizes, YFib's final state and
   AGif0n.malloc_K_t are the image-free copies in ImgBaseAGS.  cgif_file's instances are AGif2cgif.AImg_cgif and
   AGif4cgif.AImgS_cgif. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseAGS AGif2 AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {IMS : AImgS}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Geometry of the secondary block, as the walk uses it (AGjm's, with the walk's own arguments).                    *)

(* The page hull of the new block's shadow (AGjs.SHLO / SHHI). *)
Definition SHLO (a : Z) : Z := shadow_addr a / 4096 * 4096.
Definition SHHI (a sz : Z) : Z := (shadow_addr a + sz / 8 + 4095) / 4096 * 4096.
(* The next pointer-array commit (AGjp.QR) and the depot's write zone (AGjp.DX). *)
Definition QRz (ly : alayout) (res a : Z) : Prop :=
ly_Q ly + 8 * res <= a < ly_Q ly + 8 * res + 8 * kPtrArrayEntriesPerCommit /\ a < ly_Q ly + kPtrArrayResv.
Definition DXz (ly : alayout) (sp0 a : Z) : Prop := (sp0 - 128 - DEP_STK <= a < sp0 - 128) \/ ims_dzone ly a.
(* The const cells' zone of the SECONDARY walk (AGju.CZ, instance-relative): AGif0cgif.CZONE minus the instance
   windows the walk has already written when it calls the depot (the counters, the stats, the by_size_log slot,
   the mutex word and the combined stats).  The mutex's three pad bytes are const cells inside that hole, so
   ifs_depot asks for them separately. *)
Definition CZS (ly : alayout) (inst a : Z) : Prop :=
((0x10000 <= a < inst + o_sec_reserved) \/ (inst + o_sec_sorted + 1 <= a < inst + o_sec_stats) \/
 (inst + o_sec_stats + 32 <= a < inst + 296) \/ (inst + 408 <= a < inst + o_sec_mutex) \/
 (inst + o_sec_mutex + 4 <= a < inst + o_comb_stats) \/ (inst + o_comb_stats + 40 <= a < ims_img_end)) \/
(ims_shb <= a < ims_csh_end) \/ (ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/
(im_tsd <= a < im_tsd + 8) \/ (ly_D ly <= a < ly_D ly + 4096).

(* The model's state after the secondary allocation: ImgBaseAGS.sfinal over the walk's sizes, and the grown layout. *)
Definition SFSz (S : astate) (n : Z) (tr : list Z) (z : Z) (grow : bool) : astate :=
ImgBaseAGS.sfinal S n tr z (ImgBaseAGS.MSv n) (ImgBaseAGS.NDv n) grow.
Definition lyFz (ly : alayout) (S : astate) (mb : Z) : alayout := set_ly_sec ly (ImgBaseAGS.rS S) mb.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine post at Allocate's ret on the secondary grant path (AGjy.fin_facts, instance-relative and over the
   abstract depot post [DPOST]).                                                                                   *)
Record sfin (W : world im_segs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
(inst n : Z) (tr : list Z) (idx res mb : Z) (DPOST : Z -> (word -> option byte) -> Prop) (grow : bool) (z : Z)
(Wz : world im_segs) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := mkSfin {
  sf_dep : exists memD, DPOST z memD /\
    (forall a, ims_dzone ly a -> apresent (w_H Wz) mem0 a -> apresent (w_H Wz) memD a) /\
    (forall x : word, ims_dzone ly (bv_unsigned x) -> mem' x = memD x);
  sf_MEQF : forall x : word, ~ ImgBaseAGS.WIN ly regs0 n idx mb (bv_unsigned x) ->
    ~ (grow = true /\ QRz ly res (bv_unsigned x)) -> ~ DXz ly (bv_unsigned (getr regs0 2)) (bv_unsigned x) ->
    mem' x = mem0 x;
  sf_PRS : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H Wz) mem' a;
  sf_PRmap : forall a, mb <= a < mb + ImgBaseAGS.MSv n -> apresent (w_H Wz) mem' a;
  sf_PRsh : forall a, ImgBaseAGS.SMv mb <= a < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8 -> apresent (w_H Wz) mem' a;
  sf_PRq : grow = true -> forall a, QRz ly res a -> apresent (w_H Wz) mem' a;
  sf_PRW : forall a, ImgBaseAGS.WINT ly a \/ (ImgBaseAGS.QSv ly idx <= a < ImgBaseAGS.QSv ly idx + 8) -> apresent (w_H Wz) mem' a;
  sf_VISW : forall a, ImgBaseAGS.WINI regs0 n a -> aview im_segs (w_H Wz) mem' a <> None;
  sf_R10 : getr regs' 10 = w64 (ImgBaseAGS.Uv mb);
  sf_RCS : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r;
  sf_Vsh : forall x : word, (ImgBaseAGS.SMv mb <= bv_unsigned x < ImgBaseAGS.SMv mb + 768 \/
    ImgBaseAGS.SHBv + ImgBaseAGS.UEv n mb / 8 <= bv_unsigned x < ImgBaseAGS.SMv mb + ImgBaseAGS.MSv n / 8) -> mem' x = Some (Z_to_bv 8 250);
  sf_Vzs : forall x : word, ImgBaseAGS.SMv mb + 768 <= bv_unsigned x < ImgBaseAGS.SMv mb + 768 + ImgBaseAGS.N8D n / 8 -> mem' x = Some (Z_to_bv 8 0);
  sf_Vpb : n mod 8 <> 0 -> val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.PBv n mb) 1 (n mod 8);
  sf_Vunw : val_mem im_segs (mrestrict (w_H Wz) mem') (ly_T ly + t_unwinding) 1 0;
  sf_Vres : val_mem im_segs (mrestrict (w_H Wz) mem') (inst + o_sec_reserved) 8
    (if grow then res + kPtrArrayEntriesPerCommit else res);
  sf_Vnch : val_mem im_segs (mrestrict (w_H Wz) mem') (inst + o_sec_n) 8 (idx + 1);
  sf_Vmtx : val_mem im_segs (mrestrict (w_H Wz) mem') (inst + o_sec_mutex) 1 0;
  sf_Vpad : forall k, 1 <= k < 4 -> aview im_segs (w_H Wz) mem' (inst + o_sec_mutex + k) = Some 0;
  sf_Vslot : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.QSv ly idx) 8 mb;
  sf_Vh0 : val_mem im_segs (mrestrict (w_H Wz) mem') mb 8 mb;
  sf_Vh8 : val_mem im_segs (mrestrict (w_H Wz) mem') (mb + 8) 8 (ImgBaseAGS.MSv n);
  sf_Vh16 : val_mem im_segs (mrestrict (w_H Wz) mem') (mb + 16) 8 (ImgBaseAGS.NDv n);
  sf_Vh24 : val_mem im_segs (mrestrict (w_H Wz) mem') (mb + 24) 8 idx;
  sf_Vmag : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Kv mb) 8 0xCC6E96B9CC6E96B9;
  sf_Vbk : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Kv mb + 8) 8 (ImgBaseAGS.Uv mb - 16);
  sf_Vst : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Uv mb - 16) 1 2;
  sf_Vb1 : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Uv mb - 15) 1 17;
  sf_Vb2 : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Uv mb - 14) 2 0;
  sf_Vn : val_mem im_segs (mrestrict (w_H Wz) mem') (ImgBaseAGS.Uv mb - 12) 4 n;
  (* the 0xbe fill of the block's first page happens only when the call site asks for it (can_fill = x15) *)
  sf_Vfill : bv_unsigned (getr regs0 15) <> 0 ->
    forall x : word, ImgBaseAGS.Uv mb <= bv_unsigned x < ImgBaseAGS.Uv mb + 4096 -> mem' x = Some (Z_to_bv 8 190)
}.

(* The machine post at Allocate's ret on the refusal path (AGjj.PNULLX at AGjm.at_RETS), instance-relative. *)
Record snull (W : world im_segs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
(inst n : Z) (idx res mb : Z) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := mkSnull {
  sn_R10 : getr regs' 10 = w64 0;
  sn_RCS : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r;
  (* Allocate's refusal path writes the out-of-memory byte; errno is set by the caller (asan_malloc's
     SetErrnoOnNull) after the ret, and the walk's window keeps the errno bytes out of this frame clause. *)
  sn_MEQ : forall x : word, ~ ImgBaseAGS.WINP ly regs0 n (bv_unsigned x) -> bv_unsigned x <> im_oom ->
    ~ (im_errno <= bv_unsigned x < im_errno + 4) -> mem' x = mem0 x;
  sn_PRS : forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem' a;
  sn_PRW : forall a, ImgBaseAGS.WINT ly a -> apresent (w_H W) mem' a;
  sn_VISI : forall a, ImgBaseAGS.WINI regs0 n a -> aview im_segs (w_H W) mem' a <> None;
  sn_Voom : val_mem im_segs (mrestrict (w_H W) mem') im_oom 1 1;
  sn_Vunw : val_mem im_segs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0;
  sn_Vres : val_mem im_segs (mrestrict (w_H W) mem') (inst + o_sec_reserved) 8 res;
  sn_Vnch : val_mem im_segs (mrestrict (w_H W) mem') (inst + o_sec_n) 8 idx;
  sn_Vmtx : val_mem im_segs (mrestrict (w_H W) mem') (inst + o_sec_mutex) 4 0
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The kernel's effect.  [sec_md] is the model the walk hands to the leaf: the anonymous map of the block, and,
   when the pointer array was full, the fixed-in commit of its next 131072 bytes.  [skern] is the world's. *)
Definition sec_md (grow : bool) (md0 : Model) (mat matV mat' : list word) (mb msz qs : Z) : Model :=
let mdN := with_vm_backing (m_vm_lazy md0) mat md0 in
let md2 := mmap_model (w64 mb) (w64 msz) mdN in
if grow
then let mdV := with_vm_backing (m_vm_lazy md2) matV md2 in
     let md5 := grant_md false (Z_to_bv 64 50) (w64 qs) (w64 131072) mdV in
     with_vm_backing (m_vm_lazy md5) mat' md5
else with_vm_backing (m_vm_lazy md2) mat' md2.

Record skern (grow : bool) (W Wz : world im_segs) (md0 mdz : Model) (ly : alayout)
(mb msz qs : Z) : Prop := mkSkern {
  (* the granted base is a machine address: the walk reads it out of a0 *)
  sk_mbr : 0 <= mb < 2 ^ 64;
  (* the map's grant, its model, and (grow arm) the commit's eager-memory cost: the walk has each from the two
     kernel nodes (AGjs.nodeS's amwf of the map's model, AGjt.nodeV's eager bound), the instance cannot rebuild
     the eager bound without the world's AI at the commit *)
  sk_md : exists mat matV mat', mdz = sec_md grow md0 mat matV mat' mb msz qs /\
    grant_ok_na_pin (with_vm_backing (m_vm_lazy md0) mat md0) (w64 mb) msz = true /\
    amwf (mmap_model (w64 mb) (w64 msz) (with_vm_backing (m_vm_lazy md0) mat md0)) /\
    (grow = true -> eager_used mdz <= eager_used (mmap_model (w64 mb) (w64 msz) (with_vm_backing (m_vm_lazy md0) mat md0)) + 131072);
  sk_wle : wle W Wz;
  sk_io : same_io md0 mdz;
  sk_mwf : amwf mdz;
  sk_mon : forall x : word, w_H W x = false -> w_H Wz x = false;
  sk_vismap : forall x : word, mb <= bv_unsigned x < mb + msz -> w_H Wz x = false;
  sk_vissh : forall x : word, SHLO mb <= bv_unsigned x < SHHI mb msz -> w_H Wz x = false;
  sk_visq : grow = true -> forall x : word, qs <= bv_unsigned x < qs + 131072 -> w_H Wz x = false;
  sk_ab : A_bytes (w_A Wz) = A_bytes (w_A W) + msz + (SHHI mb msz - SHLO mb) + (if grow then 131072 else 0);
  sk_inc : forall i, In i (w_A W) -> In i (w_A Wz);
  sk_amap : In (mb, mb + msz) (w_A Wz);
  sk_ahull : In (SHLO mb, SHHI mb msz) (w_A Wz);
  sk_out : forall x : word, ~ (mb <= bv_unsigned x < mb + msz) -> ~ (SHLO mb <= bv_unsigned x < SHHI mb msz) ->
    ~ (grow = true /\ qs <= bv_unsigned x < qs + 131072) -> w_H Wz x = w_H W x
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* AllocG.alloc_leaf without its model-path clause: the walk's arms prove this, and the top (AGio) adds the path
   over the WHOLE tree [mt n tr S] with AGif0n.amreal_apath_gflag.  The clauses and their order are alloc_leaf's. *)
Definition alloc_leaf0 (B : asyms)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop) (oomb inst : Z) (ly : alayout) (S : astate)
(W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z)
(r : sptr * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
alloc_post im_segs B ARX AOX inst ly S W regs mem md
(fun a => fst r <> PNull /\ sptr_addr B ly' (fst r) <= a < sptr_addr B ly' (fst r) + req_size n)
ly' (snd r) W' regs' mem' md' /\
getr regs' 10 = w64 (sptr_addr B ly' (fst r)) /\
lpost (snd r) /\
(fst r = PNull -> val_mem im_segs (mrestrict (w_H W') mem') oomb 1 1).
Lemma alloc_leaf_intro : forall B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c',
alloc_leaf0 B ARX AOX lpost oomb inst ly S W regs mem md n r W' c' ->
(exists trc, apath (mt n tr S) trc r /\ gflag trc = true) ->
alloc_leaf im_segs B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c'.
Proof.
intros B mt ARX AOX lpost oomb inst ly S W regs mem md n tr r W' c' (ly' & regs' & mem' & md' & Hc & HP & HR & HL & HO) HPATH.
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact HR|]. split; [exact HL|].
split; [exact HPATH | exact HO].
Qed.

(* The interface.                                                                                                   *)
Section b.
Variable B : asyms.
(* The trace premise (AllocG's): [U tr S] for the trace [tr] at the state [S] of the call. *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable nmax : Z.
Variable lmax : Z.
Variable lpost : astate -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable mtag : Z.
(* The spin tag of the model's shadow-remap refusal, as in AGif0n: [malloc_K_t stag] is cgif's
   YFi3.malloc_K at stag = 449860. *)
Variable stag : Z.

Record AIfaceS : Prop := {
  (* (a) the view of the pre-state, with the model's secondary counters *)
  ifs_view : forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n -> 64513 <= n < nmax ->
    sview B W ly inst mem (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S);
  (* (b) the model's tree at a secondary size *)
  ifs_shape : forall n tr S, 64513 <= n < nmax -> from_primary n = false ->
    mt n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) mtag ;;
                 ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t stag n tr ob) S;
  (* the new secondary chunk is fresh: no live chunk starts at the slot the model is about to fill, so the
     tree's [upd_chunk] appends (YFib.upd_chunk_fresh) and the final state is [SFSz] below.  cgif_file gets it
     from YFib.KS_fresh over Wf. *)
  ifs_fresh : forall inst ly S W mem md, ARX inst ly S W mem md ->
    forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec (length (st_secs S)) kPage) = false;
  (* the depot callee, at the world the secondary walk is in when it calls StackDepotPut: the block's map and
     its shadow hull (and, on the grow arm, the next pointer-array commit) are already exposed, so the world is
     [Wy] >= [W].  It is AIface.if_depot with the world free; the answer's post [dpost] stays over [W], so the
     walk has ONE depot post for both arms.  cgif_file discharges it exactly as the released AGju.D1W_ok does,
     from tfib_depot_spec, which is world-general. *)
  ifs_depot : forall inst ly S W mem0 md0 tr (Wy : world im_segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, w_H W x = false -> w_H Wy x = false) ->
    (forall x : word, ims_dzone ly (bv_unsigned x) \/ CZS ly inst (bv_unsigned x) -> mem x = mem0 x) ->
    (forall k, 1 <= k < 4 -> aview im_segs (w_H Wy) mem (inst + o_sec_mutex + k) = Some 0) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H Wy) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H Wy) mem a) ->
    SRr im_segs Wy (mkCfg (mkst regs (Z_to_bv 64 ims_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = Wy /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ ims_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
      dpost inst ly S W tr z mem');
  (* (c) the kernel: the model is well formed, has room, and its map ledger is the image's *)
  ifs_mwf : forall inst ly S W mem md, ARX inst ly S W mem md -> amwf md;
  (* the room bound needs the premise on the state: cgif_file reads it out of qmeter (rpre_cgif) *)
  ifs_room : forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n ->
    eager_used md + A_bytes (w_A W) + 2 ^ 30 <= vm_limit (m_vmmaps md);
  ifs_ledger : forall inst ly S W mem md, ARX inst ly S W mem md ->
    vm_reserved (m_vmmaps md) = segments_reserved im_segs /\
    (forall sg, In sg im_segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) /\
    In (wiv (ly_Q ly, kPtrArrayResv)) (vm_maps (m_vmmaps md)) /\
    YM05.ceil_of_top (alloc_top (m_vmmaps md));
  (* a grant of the block's size exists *)
  ifs_grant : forall inst ly S W mem md mat sz, ARX inst ly S W mem md -> 0 < sz <= ImgBaseAGS.NOB ->
    exists a, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true;
  (* and every grant is in the heap band, apart from what the allocator owns, with a zero shadow *)
  ifs_apart : forall inst ly S W mem md mat sz (a : word), ARX inst ly S W mem md ->
    0 < sz <= MALLOC_MAX + 4 * 4096 -> sz mod 4096 = 0 ->
    grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true ->
    ims_zone3 (bv_unsigned a) sz /\
    Forall (zdisjoint (bv_unsigned a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
    (forall g, g mod 8 = 0 -> bv_unsigned a <= g -> g + 8 <= bv_unsigned a + sz ->
       mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0));
  (* (d) the post of the refusal arm: the state only ticked, the out-of-memory byte is the allocator's *)
  ifs_oom : forall inst ly S W mem md, ARX inst ly S W mem md -> AOX ly S im_oom;
  ifs_post_null : forall inst ly S W mem0 md0 n tr regs0 regs' mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> 64513 <= n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
    ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = w64 inst ->
    snull W ly regs0 mem0 inst n (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) 0 regs' mem' ->
    ARX inst ly (set_nev (st_nev S + 1) S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (set_nev (st_nev S + 1) S) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ ascratch B AFSTACK_G regs0 a ->
       aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem0 a) /\
    (* the same frame on the raw memory (AllocG.alloc_post's raw clause: ARX-style relations read raw bytes) *)
    (forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (set_nev (st_nev S + 1) S) (bv_unsigned x) ->
       ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> mem' x = mem0 x);
  (* the post of the grant arm: the new block, the grown layout, the final state *)
  ifs_post_grant : forall inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
    ARX inst ly S W mem0 md0 -> rpre S n -> 64513 <= n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
    ims_wframe W ly regs0 mem0 tr -> getr regs0 11 = w64 inst ->
    (grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) ->
    skern grow W Wz md0 mdz ly mb (ImgBaseAGS.MSv n) (ImgBaseAGS.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
    sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
      (fun zz m => dpost inst ly S W tr zz m) grow z Wz regs' mem' ->
    aok S (KDepot tr) z ->
    ARX inst (lyFz ly S mb) (SFSz S n tr z grow) Wz mem' mdz /\
    lpost (SFSz S n tr z grow) /\
    layout_le (length (st_secs S)) ly (lyFz ly S mb) /\
    sptr_addr B (lyFz ly S mb) (ck_user (ImgBaseAGS.KS S n)) = ImgBaseAGS.Uv mb /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S a -> ~ AOX (lyFz ly S mb) (SFSz S n tr z grow) a ->
       ~ ascratch B AFSTACK_G regs0 a -> ~ (ImgBaseAGS.Uv mb <= a < ImgBaseAGS.Uv mb + req_size n) ->
       aview im_segs (w_H Wz) mem' a = aview im_segs (w_H W) mem0 a) /\
    (* the same frame on the raw memory (AllocG.alloc_post's raw clause) *)
    (forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX (lyFz ly S mb) (SFSz S n tr z grow) (bv_unsigned x) ->
       ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) ->
       ~ (ImgBaseAGS.Uv mb <= bv_unsigned x < ImgBaseAGS.Uv mb + req_size n) -> mem' x = mem0 x)
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interface at a larger size bound [NMAXW] (AGio.alloc_sec_w).  AIfaceS states three of its fields at cgif's
   own constants: grants apart only up to MALLOC_MAX (ifs_apart), a grant exists only up to the obstacle bound
   ImgBaseAGS.NOB = 2 ^ 29 (ifs_grant), and the vm_limit room is the model's VM_HEAD = 2 ^ 30 (ifs_room).  An
   allocator whose sizes go up to NMAXW adds the same three at its own [NOBW] (its grant-existence bound) and
   [ROOMW] (its room), which the walk relates to NMAXW by the premises of AGio.alloc_sec_w. *)
Variables (NMAXW NOBW ROOMW : Z).
Definition ifs_apart_w : Prop :=
  forall inst ly S W mem md mat sz (a : word), ARX inst ly S W mem md ->
    0 < sz <= NMAXW + 4 * 4096 -> sz mod 4096 = 0 ->
    grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true ->
    ims_zone3 (bv_unsigned a) sz /\
    Forall (zdisjoint (bv_unsigned a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
    (forall g, g mod 8 = 0 -> bv_unsigned a <= g -> g + 8 <= bv_unsigned a + sz ->
       mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0)).
(* a grant of the block's size exists, up to the instance's own bound *)
Definition ifs_grant_w : Prop :=
  forall inst ly S W mem md mat sz, ARX inst ly S W mem md -> 0 < sz <= NOBW ->
    exists a, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true.
(* the instance's room below the vm limit.  The walk needs the block's map, its shadow hull and the growth of
   A_bytes, i.e. 2 * MSv + MSv / 8 + 2 pages, and on the grow arm 2 ^ 19 more for the pointer-array commit
   (AGjt.nodeV); cgif's is the model's VM_HEAD = 2 ^ 30 (YG0n.v:542, through mroom / qmeter). *)
Definition ifs_room_w : Prop :=
  forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n ->
    eager_used md + A_bytes (w_A W) + ROOMW <= vm_limit (m_vmmaps md).
Record AIfaceSw : Prop := {
  ifsw_base : AIfaceS;
  ifsw_apart : ifs_apart_w;
  ifsw_grant : ifs_grant_w;
  ifsw_room : ifs_room_w
}.
End b.

(* Every AIfaceS is an AIfaceSw at cgif's own three constants. *)
Lemma AIfaceS_w : forall B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag,
  AIfaceS B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag ->
  AIfaceSw B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag MALLOC_MAX ImgBaseAGS.NOB (2 ^ 30).
Proof.
intros B U mt ARX AOX rpre nmax lmax lpost dpost mtag stag H. constructor.
- exact H.
- exact (ifs_apart _ _ _ _ _ _ _ _ _ _ _ _ H).
- exact (ifs_grant _ _ _ _ _ _ _ _ _ _ _ _ H).
- exact (ifs_room _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.
End a.
