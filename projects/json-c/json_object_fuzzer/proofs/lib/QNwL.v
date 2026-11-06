(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q67d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q67d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation mem := (word -> option byte) (only parsing).

Definition A_TP : Z := 0x622e60.
Definition A_ERRNO : Z := 0x622dbc.
Definition A_INSTANCE : Z := 0x0ec498.
Definition A_FS_MAP_SIZE : Z := 0xb09000.
Definition A_TLS_TSD : Z := 0x622e08.
Definition A_TSD_MAIN : Z := 0x644280.

Record rlay : Type := mkRL {
rl_T    : Z;
rl_ctx  : Z;
rl_dn   : Z;
rl_ssb  : Z;
rl_dtls : Z
}.

Definition rlay_objs (RE : aentry) (X : rlay) : list (Z * Z) :=
[ (rl_T X, 0x1000); (rl_ctx X, 0x10000); (rl_dn X, 0x100000); (rl_ssb X, 0x800000);
(rl_dtls X, 0x1000); (ae_fs_base RE, A_FS_MAP_SIZE) ].

Definition prim_lo (RE : aentry) : Z := al_space_beg (ae_L RE).
Definition prim_hi (RE : aentry) : Z := al_space_beg (ae_L RE) + 2^37 + 0x1000.
Definition region_info (RE : aentry) : Z := al_space_beg (ae_L RE) + 2^37.
Definition ptrarr_lo (RE : aentry) : Z := al_ptrarr (ae_L RE).
Definition ptrarr_hi (RE : aentry) : Z := al_ptrarr (ae_L RE) + 0x800000.

Notation a_hull := ((0x10000, 0x635000) : Z * Z) (only parsing).

Definition iv_disjoint (a b : Z * Z) : Prop :=
fst a + snd a <= fst b \/ fst b + snd b <= fst a.

Fixpoint pairwise_disjoint (l : list (Z * Z)) : Prop :=
match l with
| [] => True
| x :: l' => Forall (iv_disjoint x) l' /\ pairwise_disjoint l'
end.

Definition avoid_covers {BAND : Band} (RE : aentry) (X : rlay) : Prop :=
forall o, In o (a_hull :: (0x7fff7000, KHI - 0x7fff7000) :: (band_lo, 2^64 - band_lo)
:: (prim_lo RE, 2^37 + 0x1000) :: (ptrarr_lo RE, 0x800000) :: rlay_objs RE X) ->

exists iv, In iv (al_avoid (ae_L RE)) /\ fst iv <= fst o /\ fst o + snd o <= snd iv.

Definition rlay_ok {BAND : Band} (RE : aentry) (X : rlay) : Prop :=

ae_sp0 RE - 0xa0 <= ae_stack_top RE < ae_sp0 RE + 0x8000 /\ ae_stack_top RE mod 4096 = 0
/\ band_lo + 0x800000 <= ae_sp0 RE /\ ae_sp0 RE <= 2^47 /\ ae_sp0 RE mod 16 = 0

/\ prim_lo RE mod 0x10000 = 0 /\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo
/\ ptrarr_lo RE mod 4096 = 0 /\ (lowhigh (ptrarr_lo RE) 0x800000 /\ off_hull (ptrarr_lo RE) 0x800000)
/\ ptrarr_hi RE <= band_lo
/\ (iv_disjoint (prim_lo RE, 2^37 + 0x1000) (ptrarr_lo RE, 0x800000)

/\ avoid_covers RE X)

/\ Forall (fun o => fst o mod 4096 = 0 /\ (lowhigh (fst o) (snd o) /\ off_hull (fst o) (snd o)) /\ fst o + snd o <= band_lo
/\ iv_disjoint o (prim_lo RE, 2^37 + 0x1000)
/\ iv_disjoint o (ptrarr_lo RE, 0x800000)) (rlay_objs RE X)
/\ pairwise_disjoint (rlay_objs RE X).

Definition slot_size (c : Z) : Z := class_size c.
Definition slot_beg (RE : aentry) (c i : Z) : Z := reg_beg (ae_L RE) c + i * class_size c.

Definition prim_user (sb n : Z) : Z := sb + rz_size n.
Definition chunk_hdr (user : Z) : Z := user - 16.

Definition aptr_cls (p : aptr) : Z := class_of (aptr_req p).

Inductive stag : Type :=
| TFree
| TCached
| TLive (p : aptr)
| TQuar (p : aptr)
| TQOwn.

Definition stag_eqb (a b : stag) : bool :=
match a, b with
| TFree, TFree | TCached, TCached | TQOwn, TQOwn => true
| TLive p, TLive q | TQuar p, TQuar q => aptr_eqb p q
| _, _ => false
end.

Definition tag_prim (t : stag) : bool := match t with TFree | TCached => true | _ => false end.

Definition tag_quar (t : stag) : bool := match t with TQuar _ | TQOwn => true | _ => false end.

Definition ghost : Type := Z -> list stag.
Definition ghost0 : ghost := fun _ => [].
Definition gtags (G : ghost) (c : Z) : list stag := G c.
Definition gset (c : Z) (l : list stag) (G : ghost) : ghost := fun c' => if c' =? c then l else G c'.
Definition tag_at (G : ghost) (c i : Z) : option stag :=
if i <? 0 then None else nth_error (G c) (Z.to_nat i).
Definition ncarved (G : ghost) (c : Z) : Z := Z.of_nat (length (G c)).

Fixpoint list_set {A} (l : list A) (i : nat) (v : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: list_set t i' v
end.
Definition set_tag (c i : Z) (t : stag) (G : ghost) : ghost := gset c (list_set (G c) (Z.to_nat i) t) G.

Definition count_tag (f : stag -> bool) (l : list stag) : Z := Z.of_nat (length (filter f l)).

Definition holds (p : aptr) (t : stag) : bool :=
match t with TLive q | TQuar q => aptr_eqb p q | _ => false end.

Fixpoint find_index {A} (f : A -> bool) (l : list A) (i : nat) : option nat :=
match l with
| [] => None
| x :: l' => if f x then Some i else find_index f l' (S i)
end.
Definition slot_of (G : ghost) (p : aptr) : option Z :=
option_map Z.of_nat (find_index (holds p) (G (aptr_cls p)) 0%nat).

Definition live_prim (RE : aentry) (G : ghost) (p : aptr) (A n : Z) : Prop :=
exists id i, p = APrim id n /\ 0 <= n /\ from_primary n = true
/\ tag_at G (class_of n) i = Some (TLive p) /\ 0 <= i
/\ A = prim_user (slot_beg RE (class_of n) i) n.

Definition live_sec (a : AState) (p : aptr) (A n : Z) : Prop :=
exists mb, p = ASec mb n /\ 0 <= n /\ from_primary n = false
/\ In (mkSec mb (sec_map_size n) n) (as_reg a)
/\ A = mb + kSecUserOff.

Definition sec_ok {BAND : Band} (RE : aentry) (X : rlay) (e : secent) : Prop :=
se_beg e mod 4096 = 0 /\ (lowhigh (se_beg e) (se_size e) /\ off_hull (se_beg e) (se_size e))
/\ se_beg e + se_size e <= band_lo
/\ se_size e = sec_map_size (se_req e) /\ from_primary (se_req e) = false /\ 0 <= se_req e < 2^40
/\ iv_disjoint (se_beg e, se_size e) (prim_lo RE, 2^37 + 0x1000)
/\ iv_disjoint (se_beg e, se_size e) (ptrarr_lo RE, 0x800000)
/\ Forall (iv_disjoint (se_beg e, se_size e)) (rlay_objs RE X).

Definition gcons {BAND : Band} (a : AState) (LB : list ablock) (FS : list fframe) (G : ghost) (RE : aentry) (X : rlay) : Prop :=
rlay_ok RE X

/\ (forall p A n, In (p, A, n) LB -> (live_prim RE G p A n \/ live_sec a p A n) /\ n <= 2^26)
/\ List.NoDup (map ablk_id LB)

/\ (forall c i p, tag_at G c i = Some (TLive p) -> exists id n A, p = APrim id n /\ In (p, A, n) LB /\ class_of n = c)
/\ (forall c i p, tag_at G c i = Some (TQuar p) -> aptr_cls p = c /\ from_primary (aptr_req p) = true)
/\ (forall c, G c <> [] -> 1 <= c < kNumClasses /\ ncarved G c * class_size c = c_alloc_user (cls a c))
/\ (forall c, 1 <= c < kNumClasses -> 0 <= c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset
/\ c_mapped_user (cls a c) mod kUserMapSize = 0)

/\ (forall c i c' i' p t t', tag_at G c i = Some t -> tag_at G c' i' = Some t' -> holds p t = true -> holds p t' = true ->
c = c' /\ i = i')
/\ (forall c i t id n, tag_at G c i = Some t -> holds (APrim id n) t = true -> (id < as_next a)%N)

/\ Forall (sec_ok RE X) (as_reg a)
/\ pairwise_disjoint (map (fun e => (se_beg e, se_size e)) (as_reg a))
/\ List.NoDup (map se_beg (as_reg a))

/\ (forall f, In f FS -> fframe_rangeA RE (ff_cls f) (ff_addr f))
/\ (forall f1 f2, In f1 FS -> In f2 FS -> ff_addr f1 <> ff_addr f2 ->
ff_addr f1 + ff_size (ff_cls f1) <= ff_addr f2 \/ ff_addr f2 + ff_size (ff_cls f2) <= ff_addr f1).

Definition in_iv (iv : Z * Z) (a : Z) : Prop := fst iv <= a < fst iv + snd iv.
Definition in_ivs (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ in_iv iv a.

Definition in_sh (iv : Z * Z) (a : Z) : Prop := SH (fst iv) <= a < SH (fst iv) + snd iv / 8.
Definition in_shs (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ in_sh iv a.

Definition in_slots (f : stag -> bool) (RE : aentry) (G : ghost) (a : Z) : Prop :=
exists c i t, tag_at G c i = Some t /\ f t = true /\ in_iv (slot_beg RE c i, class_size c) a.
Definition in_slots_sh (f : stag -> bool) (RE : aentry) (G : ghost) (a : Z) : Prop :=
exists c i t, tag_at G c i = Some t /\ f t = true /\ in_sh (slot_beg RE c i, class_size c) a.

Definition in_live_user (LB : list ablock) (a : Z) : Prop :=
exists b, In b LB /\ ablk_addr b <= a < ablk_addr b + ablk_size b.

Definition sec_live (LB : list ablock) (e : secent) : Prop :=
exists A, In (ASec (se_beg e) (se_req e), A, se_req e) LB.
Definition in_sec_hdr (a0 : AState) (a : Z) : Prop :=
exists e, In e (as_reg a0) /\ se_beg e <= a < se_beg e + kPage.
Definition in_sec_hdr_sh (a0 : AState) (a : Z) : Prop :=
exists e, In e (as_reg a0) /\ in_sh (se_beg e, kPage) a.
Definition in_sec_body (P : secent -> Prop) (a0 : AState) (a : Z) : Prop :=
exists e, In e (as_reg a0) /\ P e /\ se_beg e + kPage <= a < se_beg e + se_size e.
Definition in_sec_body_sh (P : secent -> Prop) (a0 : AState) (a : Z) : Prop :=
exists e, In e (as_reg a0) /\ P e /\ in_sh (se_beg e + kPage, se_size e - kPage) a.

Definition rtconst_img : list (Z * Z) :=
[ (0x0e2000, 0x5000)
; (0x0e7c08, 0xbc8)
; (A_INSTANCE, 0x68)
; (A_INSTANCE + 792, 24)
; (A_INSTANCE + 3616, 14)
; (0x0ed2f8, 0x78)
; (0x0ef35c, 12)
; (0x0efaf8, 12)
; (0x0f07d8, 0x28)
; (0x171d61, 2)
; (0x17f590, 0x18)
; (0x1815c0, 0x60)
; (0x181628, 0x120)
; (A_TLS_TSD, 8)
; (0x622e58, 0x40)
; (A_TSD_MAIN, 8)

; (0x0ec440, 8)
; (0x0ed3b0, 0x20)
; (0x0ed3f0, 4)
; (0x642ea0, 8)
; (0x643120, 8)

; (0x0e7c00, 8)
].
Definition fp_RTconst (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_ivs rtconst_img a
\/ in_iv (rl_T X, 80) a
\/ in_iv (rl_ctx X, 0xa0) a
\/ in_iv (rl_dtls X, 0x1000) a.

Definition fp_RStats (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_iv (rl_T X + 2800, 368) a \/ in_iv (A_ERRNO, 4) a \/ a = 0x171d60.

Definition in_regions (RE : aentry) (a : Z) : Prop :=
exists c, 1 <= c < kNumClasses /\ reg_beg (ae_L RE) c <= a < reg_beg (ae_L RE) c + kFreeArrayOffset.
Definition in_regions_sh (RE : aentry) (a : Z) : Prop :=
exists c, 1 <= c < kNumClasses /\ in_sh (reg_beg (ae_L RE) c, kFreeArrayOffset) a.
Definition in_fas (RE : aentry) (a : Z) : Prop :=
exists c, 1 <= c < kNumClasses /\ fa_beg (ae_L RE) c <= a < fa_beg (ae_L RE) c + kFreeArraySize.
Definition in_fas_sh (RE : aentry) (a : Z) : Prop :=
exists c, 1 <= c < kNumClasses /\ in_sh (fa_beg (ae_L RE) c, kFreeArraySize) a.

Definition fp_RPrim (G : ghost) (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_iv (region_info RE, 0x1000) a
\/ in_iv (rl_T X + 208, 2592) a
\/ in_fas RE a \/ in_fas_sh RE a
\/ (in_regions RE a /\ ~ in_slots (fun t => negb (tag_prim t)) RE G a)
\/ (in_regions_sh RE a /\ ~ in_slots_sh (fun t => negb (tag_prim t)) RE G a).

Definition is_live (t : stag) : bool := match t with TLive _ => true | _ => false end.
Definition fp_RChunks (a0 : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay) (a : Z) : Prop :=
((in_slots is_live RE G a \/ in_sec_body (sec_live LB) a0 a) /\ ~ in_live_user LB a)
\/ in_slots_sh is_live RE G a
\/ in_sec_body_sh (sec_live LB) a0 a.

Definition fp_RSec (a0 : AState) (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_iv (A_INSTANCE + 104, 624) a
\/ in_iv (ptrarr_lo RE, 0x800000) a
\/ in_sec_hdr a0 a \/ in_sec_hdr_sh a0 a.

Definition fp_RQuar (a0 : AState) (LB : list ablock) (G : ghost) (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_iv (rl_T X + 80, 128) a
\/ in_iv (A_INSTANCE + 728, 64) a \/ in_iv (A_INSTANCE + 816, 2800) a
\/ in_iv (0x0f0d00, 0x81038) a \/ in_iv (0x17f588, 4) a
\/ in_slots tag_quar RE G a \/ in_slots_sh tag_quar RE G a
\/ in_sec_body (fun e => ~ sec_live LB e) a0 a \/ in_sec_body_sh (fun e => ~ sec_live LB e) a0 a.

Definition fp_RDepot (RE : aentry) (X : rlay) (a : Z) : Prop :=
in_iv (0x1c19c8, 0x450028) a
\/ in_iv (rl_dn X, 0x100000) a
\/ in_iv (rl_ssb X, 0x800000) a
\/ a = rl_T X + 3168.

Definition fp_RFake (FS : list fframe) (RE : aentry) (X : rlay) (a : Z) : Prop :=
(in_iv (ae_fs_base RE, A_FS_MAP_SIZE) a /\ ~ in_fframe_body FS a)
\/ (in_sh (ae_fs_base RE, A_FS_MAP_SIZE) a /\ ~ in_fframe_shadow FS a).

Definition bst_cells (obj sz : Z) (trace : list byte) (topbp : Z) : list cell :=
[C8 (Z_to_bv 64 (obj + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0); CB 2040 trace; C8 (Z_to_bv 64 topbp)].

Local Notation agree := (agree_on asegs).

Definition same_tags (f : stag -> bool) (G G' : ghost) : Prop :=
forall c i t, f t = true -> (tag_at G c i = Some t <-> tag_at G' c i = Some t).
Definition same_len (G G' : ghost) : Prop := forall c, length (G c) = length (G' c).

Lemma same_tags_refl : forall f G, same_tags f G G.
Proof. intros f G c i t _. tauto. Qed.

Lemma same_len_refl : forall G, same_len G G.
Proof. intros G c. reflexivity. Qed.

Record arun_components {BAND : Band} : Type := mkAC {

ac_RTconst : aentry -> rlay -> mem -> Prop;
ac_RStats  : aentry -> rlay -> mem -> Prop;
ac_RPrim   : AState -> ghost -> aentry -> rlay -> mem -> Prop;
ac_RChunks : AState -> list ablock -> ghost -> aentry -> rlay -> mem -> Prop;
ac_RSec    : AState -> list ablock -> aentry -> rlay -> mem -> Prop;
ac_RQuar   : AState -> list ablock -> ghost -> aentry -> rlay -> mem -> Prop;
ac_RDepot  : aentry -> rlay -> mem -> Prop;
ac_RFake   : list fframe -> aentry -> rlay -> mem -> Prop;

ac_RTconst_frame : forall RE X m m', ac_RTconst RE X m -> wmono asegs m m' -> agree (fp_RTconst RE X) m m' -> ac_RTconst RE X m';
ac_RStats_frame  : forall RE X m m', ac_RStats RE X m -> wmono asegs m m' -> agree (fp_RStats RE X) m m' -> ac_RStats RE X m';
ac_RPrim_frame   : forall a G RE X m m', ac_RPrim a G RE X m -> wmono asegs m m' -> agree (fp_RPrim G RE X) m m' -> ac_RPrim a G RE X m';
ac_RChunks_frame : forall a LB G RE X m m', ac_RChunks a LB G RE X m -> wmono asegs m m' -> agree (fp_RChunks a LB G RE X) m m' ->
ac_RChunks a LB G RE X m';
ac_RSec_frame    : forall a LB RE X m m', ac_RSec a LB RE X m -> wmono asegs m m' -> agree (fp_RSec a RE X) m m' -> ac_RSec a LB RE X m';
ac_RQuar_frame   : forall a LB G RE X m m', ac_RQuar a LB G RE X m -> wmono asegs m m' -> agree (fp_RQuar a LB G RE X) m m' ->
ac_RQuar a LB G RE X m';
ac_RDepot_frame  : forall RE X m m', ac_RDepot RE X m -> wmono asegs m m' -> agree (fp_RDepot RE X) m m' -> ac_RDepot RE X m';
ac_RFake_frame   : forall FS RE X m m', ac_RFake FS RE X m -> wmono asegs m m' -> agree (fp_RFake FS RE X) m m' -> ac_RFake FS RE X m';

ac_RTconst_shadow : forall RE X m, ac_RTconst RE X m -> shadow_base asegs m;

ac_RPrim_ext : forall a a' G G' RE X m, ac_RPrim a G RE X m ->
(forall c, cls a' c = cls a c) -> as_cache_inited a' = as_cache_inited a ->
same_len G G' -> same_tags tag_prim G G' -> ac_RPrim a' G' RE X m;
ac_RChunks_ext : forall a a' LB G G' RE X m, ac_RChunks a LB G RE X m ->
(forall e, In e (as_reg a) -> In e (as_reg a')) -> same_tags is_live G G' -> ac_RChunks a' LB G' RE X m;
ac_RSec_ext : forall a a' LB LB' RE X m, ac_RSec a LB RE X m ->
as_reg a' = as_reg a -> as_nres a' = as_nres a -> as_spent a' = as_spent a -> ac_RSec a' LB' RE X m;

ac_RQuar_ext : forall a a' LB LB' G G' RE X m, ac_RQuar a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ->
(forall e, In e (as_reg a) -> (sec_live LB e <-> sec_live LB' e)) -> same_tags tag_quar G G' ->
ac_RQuar a' LB' G' RE X m;

ac_RQuar_alloc_sec : forall a a' LB G RE X m mb msz n A, ac_RQuar a LB G RE X m ->
as_tq a' = as_tq a -> as_gq a' = as_gq a -> as_reg a' = as_reg a ++ [mkSec mb msz n] ->
~ In mb (map se_beg (as_reg a)) -> ac_RQuar a' ((ASec mb n, A, n) :: LB) G RE X m;

ac_RChunks_perm : forall a LB LB' G RE X m, ac_RChunks a LB G RE X m -> Permutation LB LB' -> ac_RChunks a LB' G RE X m;
ac_RSec_perm    : forall a LB LB' RE X m, ac_RSec a LB RE X m -> Permutation LB LB' -> ac_RSec a LB' RE X m;
ac_RQuar_perm   : forall a LB LB' G RE X m, ac_RQuar a LB G RE X m -> Permutation LB LB' -> ac_RQuar a LB' G RE X m;
ac_RFake_perm   : forall FS FS' RE X m, ac_RFake FS RE X m -> Permutation FS FS' -> ac_RFake FS' RE X m;

ac_RChunks_shadow : forall a LB FS G RE X m p A n,
gcons a LB FS G RE X -> ac_RChunks a LB G RE X m -> In (p, A, n) LB -> blk_shadow asegs m A n;

ac_RFake_release0 : forall FS RE X m f (flag : word),
(forall f', In f' FS -> fframe_rangeA RE (ff_cls f') (ff_addr f')) ->
ac_RFake FS RE X m -> In (0, f) FS ->
bytes_at asegs m (f + ff_size 0 - 8) (le8 flag) ->
ac_RFake (ffs_remove f FS) RE X (write_to_mem m flag [Z_to_bv 8 0])
/\ wview asegs m flag <> None
/\ fp_RFake FS RE X (bv_unsigned flag)
}.
