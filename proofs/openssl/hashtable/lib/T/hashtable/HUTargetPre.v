(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec StoreOk Frame MallocDefs AgentLib MmapSim ShapeAlg Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

(* [comment removed for export] *)
Definition stack_writableZ (M : word -> option byte) (sp0 : Z) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (sp0 - 8388608 + d)) m = true.

(* [comment removed for export] *)
Record tgt_entry (sp0 buf can : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TGT_ENTRY {
  (* [comment removed for export] *)
  te_ra : getr R 1 = Z_to_bv 64 0xe1b18;
  te_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  te_gp : getr R 3 = Z_to_bv 64 0x10800;
  te_tp : getr R 4 = Z_to_bv 64 0x331ae8;
  te_a0 : getr R 10 = Z_to_bv 64 (buf + 2);                                (* [comment removed for export] *)
  te_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);                     (* [comment removed for export] *)
  te_a2 : getr R 12 = Z_to_bv 64 (buf + 6 + hdr_cfglen content);           (* [comment removed for export] *)
  te_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);                     (* [comment removed for export] *)
  te_s0 : getr R 8 = Z_to_bv 64 (buf + 2);
  te_s1 : getr R 9 = Z_to_bv 64 buf;
  te_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
  te_s3 : getr R 19 = Z_to_bv 64 (buf + 6 + hdr_cfglen content);
  te_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
  te_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
            (* [comment removed for export] *)
  te_s6 : getr R 22 = Z_to_bv 64 0x31ef09;                                  (* [comment removed for export] *)
  te_s7 : getr R 23 = Z_to_bv 64 0;                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  te_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  te_len : 6 + hdr_cfglen content <= Z.of_nat (length content) < 67108864;
  te_buf : buf mod 16 = 0 /\ 0x354000 <= buf /\ buf + Z.of_nat (length content) <= sp0 - 8388608;
  te_can : 0 <= can < 2 ^ 64;
  (* [comment removed for export] *)
  te_stack : stack_writableZ M sp0;
  te_img   : forall i, 0x10000 <= i < 0x31eec0 -> M (Z_to_bv 64 i) = None;
             (* [comment removed for export] *)
  te_init0 : M (Z_to_bv 64 0x32ef10) = None;                                (* [comment removed for export] *)
  te_canary : rdn RSEGS M (Z_to_bv 64 0x351b28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  te_content : rdn RSEGS M (Z_to_bv 64 buf) (length content) = Some content
}.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_ledger (mb bw : word) (VM : VmMaps) : Prop :=
  (4096 <= bv_unsigned (vm_start_brk VM) /\ bv_unsigned (vm_start_brk VM) mod 4096 = 0
   /\ bv_unsigned (vm_start_brk VM) + 8192 <= 0x7fff7f800000)
  /\ ( (bv_unsigned bw = bv_unsigned mb + 8192 /\ vm_start_brk VM = mb
        /\ bv_unsigned (vm_brk VM) = bv_unsigned mb + 8192)
     \/ (bv_unsigned bw = 2 ^ 64 - 1 /\ In (mb, Z_to_bv 64 8192) (vm_maps VM)
         /\ exists lo sz, In (lo, sz) (vm_noaccess VM)
              /\ bv_unsigned lo <= bv_unsigned mb /\ bv_unsigned mb + 4096 <= bv_unsigned lo + bv_unsigned sz) ).

(* [comment removed for export] *)
Lemma In_map_remove_keep : forall l (p : word * word) (B : word),
  In p l -> fst p <> B -> In p (map_remove l B).
Proof.
  intros l p B Hin Hne. unfold map_remove. apply filter_In. split; [exact Hin|].
  apply Bool.negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros E. apply Hne. apply bv_eq. exact E.
Qed.

Lemma maps_subtract_keep_cover : forall l lo hi mbz,
  0 <= lo -> lo <= hi -> hi < 2 ^ 64 ->
  (exists a sz, In (a, sz) l /\ bv_unsigned a <= mbz /\ mbz + 4096 <= bv_unsigned a + bv_unsigned sz) ->
  (mbz + 4096 <= lo \/ hi <= mbz) ->
  exists a sz, In (a, sz) (maps_subtract l lo hi) /\ bv_unsigned a <= mbz /\ mbz + 4096 <= bv_unsigned a + bv_unsigned sz.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi mbz Hlo Hlh Hhi (p & s & Hp & H1 & H2) Hd; [destruct Hp|].
  cbn [maps_subtract]. destruct Hp as [E | Hp].
  - injection E as -> ->. pose proof (u64_range p). pose proof (u64_range s). unfold iv_subtract. destruct Hd as [Hd | Hd].
    + exists p, (Z_to_bv 64 (Z.min (bv_unsigned s) (lo - bv_unsigned p))). split.
      * apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _)) by lia. apply in_or_app. left. left. reflexivity.
      * rewrite u64_lit by lia. lia.
    + exists (Z_to_bv 64 (Z.max (bv_unsigned p) hi)), (Z_to_bv 64 (bv_unsigned p + bv_unsigned s - Z.max (bv_unsigned p) hi)). split.
      * apply in_or_app. left. apply in_or_app. right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. reflexivity.
      * rewrite !u64_lit by lia. lia.
  - destruct (IH lo hi mbz Hlo Hlh Hhi ltac:(exists p, s; auto) Hd) as (a' & s' & Ha & A1 & A2).
    exists a', s'. split; [apply in_or_app; right; exact Ha | lia].
Qed.

Lemma vm_ledger_frame : forall mb bw VM res' maps' noacc' lim' base' isp',
  vm_ledger mb bw VM ->
  (In (mb, Z_to_bv 64 8192) (vm_maps VM) -> In (mb, Z_to_bv 64 8192) maps') ->
  (In (mb, Z_to_bv 64 8192) (vm_maps VM) ->
   (exists lo sz, In (lo, sz) (vm_noaccess VM) /\ bv_unsigned lo <= bv_unsigned mb /\ bv_unsigned mb + 4096 <= bv_unsigned lo + bv_unsigned sz) ->
   exists lo sz, In (lo, sz) noacc' /\ bv_unsigned lo <= bv_unsigned mb /\ bv_unsigned mb + 4096 <= bv_unsigned lo + bv_unsigned sz) ->
  vm_ledger mb bw (mkVmMapsFull res' maps' noacc' (vm_start_brk VM) (vm_brk VM) lim' base' isp').
Proof.
  intros mb bw VM res' maps' noacc' lim' base' isp' [Hs Hw] Hm Hn. split; [exact Hs|]. cbn [vm_maps vm_noaccess vm_start_brk vm_brk].
  destruct Hw as [Hw | (H1 & H2 & H3)]; [left; exact Hw | right]. split; [exact H1|]. split; [apply Hm, H2 | apply Hn; [exact H2 | exact H3]].
Qed.

(* [comment removed for export] *)
Lemma seps_in_disjoint : forall l p q, seps l -> In p l -> In q l -> p <> q -> iv_disjoint p q.
Proof.
  intros l p q H. induction H as [|r l Hr Hl IH]; intros Hp Hq Hne; [destruct Hp|].
  destruct Hp as [<- | Hp], Hq as [<- | Hq].
  - exfalso. apply Hne. reflexivity.
  - exact (proj1 (Forall_forall _ _) Hr q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hr p Hp) as D. unfold iv_disjoint in *. lia.
  - apply IH; assumption.
Qed.

Lemma vm_ledger_mmap : forall mb bw VM res' p lim' base' isp',
  vm_ledger mb bw VM ->
  vm_ledger mb bw (mkVmMapsFull res' (p :: vm_maps VM) (vm_noaccess VM) (vm_start_brk VM) (vm_brk VM) lim' base' isp').
Proof. intros mb bw VM res' p lim' base' isp' H. apply vm_ledger_frame; [exact H | intros Hin; right; exact Hin | auto]. Qed.

