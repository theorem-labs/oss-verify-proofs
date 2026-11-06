(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the twin of lib/U/Reusable/YL0i.v (posts, contracts), lib/U/Reusable/YL05.v (lib_post_state) and lib/U/Reusable/YL06.v (call site) for a return value of the fuzz target of 0 or -1 *)
(* Donor: reac-repacer/fuzz_lock, proofs/reac-repacer/fuzz_lock/lib/U/Reusable/YL0i.v, U/Reusable/YL05.v and
   U/Reusable/YL06.v at 901d1549395.
   Module: OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog.FrameRetD1. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import
YK11 YK0i YK0o YK0s YK15 YM06 YM02 YP0m YP0e YP09 YP0l YP0k YP06 YP03 YP08 YN3v.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YN03 YL07 YL01 YL0d YL00 YL0g YL05 YI06 YI16 YI14 YL0i YL06.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import AllocSlots.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

(* YL0i.v lib_post_x_G, for the return value r *)
Definition lib_post_x_G_r (r : Z) (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 (ll_ret l) /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = r /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok_slots A' (lib_delta n b) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).

(* YL0i.v lib_contract_x_G, the call on pl with the post for ret pl *)
Definition lib_contract_x_G_r (ret : list byte -> Z) (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b (K : lleaf -> TSet),
lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
GI j mem ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_G_r (ret pl) G (f pl) stk L A regs mem md p n b l L' A' regs' mem' md' /\
GI (S j) mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

(* YL0i.v lib_post_x_T, for the return value r *)
Definition lib_post_x_T_r (r : Z) (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf) (T T' : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 (ll_ret l) /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T ->
exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = r /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok_slots A' (TD T T' (lib_delta n b)) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
tb_live L' A' T' /\
(forall t, In t T' -> In t (blocks L A) -> In t T).

(* YL0i.v lib_contract_x_T, the call on pl with the post for ret pl *)
Definition lib_contract_x_T_r (ret : list byte -> Z) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b T (K : lleaf -> TSet),
lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
GI j T mem ->
tb_live L A T ->
(0 < n -> ~ In (p, n) T) ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md' T',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_T_r (ret pl) G (f pl) stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
GI (S j) T' mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Lemma lib_post_x_T_r_of_G : forall r G out stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x_G_r r G out stk L A regs mem md p n b l L' A' regs' mem' md' ->
lib_post_x_T_r r G out stk L A regs mem md p n b l [] [] L' A' regs' mem' md'.
Proof using.
intros r G out stk L A regs mem md p n b l L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj (fun q k Hq _ => H8 q k Hq)
(conj H9 (conj H10 (conj (fun q k i Hq _ => H11 q k i Hq) (conj H12 (conj H13 (conj H14 (conj H15 (conj H16
(conj H17 (conj H18 (conj (tb_live_nil L' A') _))))))))))))))))))).
intros t Ht. destruct Ht.
Qed.

Lemma lib_contract_x_T_r_of_G : forall ret G R GI f j pc ra empty stk,
lib_contract_x_G_r ret G R GI f j pc ra empty stk ->
lib_contract_x_T_r ret G R (fun j T m => T = [] /\ GI j m) f j pc ra empty stk.
Proof using.
intros ret G R GI f j pc ra empty stk H L A regs mem md p n pl b T K Hpre [HT HGI] _ _ HR Hfrm HK.
subst T.
apply (H L A regs mem md p n pl b K Hpre HGI HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_T_r_of_G (ret pl) G (f pl) stk L A regs mem md p n b l L' A' regs' mem' md' Hp)
  | split; [reflexivity | exact HGI']].
Qed.

(* YL0i.v lib_post_x_R, for the return value r *)
Definition lib_post_x_R_r (r : Z) (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (l : lleaf) (T T' : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 (ll_ret l) /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T ->
exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = r /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
tb_live L' A' T' /\
(forall t, In t T' -> In t (blocks L A) -> In t T).

(* YL0i.v lib_contract_x_R, the call on pl with the post for ret pl *)
Definition lib_contract_x_R_r (ret : list byte -> Z) (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop)
(G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl T (K : lleaf -> TSet),
lib_pre_w B API stk empty L A regs mem md ra p n pl ->
RI pl j T A ->
GI j T mem ->
tb_live L A T ->
(0 < n -> ~ In (p, n) T) ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md' T',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_R_r (ret pl) G (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' /\
RI pl (S j) T' A' /\
GI (S j) T' mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Lemma lib_post_x_R_r_of_T : forall r G out stk L A regs mem md p n b l T T' L' A' regs' mem' md',
lib_post_x_T_r r G out stk L A regs mem md p n b l T T' L' A' regs' mem' md' ->
lib_post_x_R_r r G out stk L A regs mem md p n l T T' L' A' regs' mem' md' /\ res_ok_slots A' (TD T T' (lib_delta n b)).
Proof using.
intros r G out stk L A regs mem md p n b l T T' L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
split; [|exact H17].
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
(conj H13 (conj H14 (conj H15 (conj H16 (conj H18 (conj H19 H20)))))))))))))))))).
Qed.

Lemma lib_contract_x_R_r_of_T : forall ret (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) G R GI f j pc ra empty stk,
(forall pl T A m, RI pl j T A -> GI j T m -> exists b, res_ok_slots A b /\ lib_room b (Z.of_nat (length pl)) /\
forall T' A' m', res_ok_slots A' (TD T T' (lib_delta (Z.of_nat (length pl)) b)) -> GI (S j) T' m' -> RI pl (S j) T' A') ->
lib_contract_x_T_r ret G R GI f j pc ra empty stk -> lib_contract_x_R_r ret RI G R GI f j pc ra empty stk.
Proof using.
intros ret RI G R GI f j pc ra empty stk HRI H L A regs mem md p n pl T K Hpre HR0 HGI HTL HpT HR Hfrm HK.
pose proof Hpre as (_ & Hn & _).
destruct (HRI pl T A mem HR0 HGI) as (b & Hb & Hroom & Hnext). rewrite <- Hn in Hroom, Hnext.
apply (H L A regs mem md p n pl b T K (lib_pre_x_of_w B API stk empty L A regs mem md ra p n pl b Hpre Hb Hroom) HGI HTL HpT HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HGI').
destruct (lib_post_x_R_r_of_T (ret pl) G (f pl) stk L A regs mem md p n b l T T' L' A' regs' mem' md' Hp) as [Hp' Hres].
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
exact (conj Hp' (conj (Hnext T' A' mem' Hres HGI') HGI')).
Qed.

Lemma lib_post_x_R_r_mono : forall r G G' out stk L A regs mem md p n l T T' L' A' regs' mem' md',
(forall a, in_globals G a -> in_globals G' a) ->
lib_post_x_R_r r G out stk L A regs mem md p n l T T' L' A' regs' mem' md' ->
lib_post_x_R_r r G' out stk L A regs mem md p n l T T' L' A' regs' mem' md'.
Proof using.
intros r G G' out stk L A regs mem md p n l T T' L' A' regs' mem' md' HG
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ H11)))))))))).
intros a Ha Hs Hc He Hg. exact (H10 a Ha Hs Hc He (fun h => Hg (HG a h))).
Qed.

Lemma lib_contract_x_R_r_mono : forall ret RI G G' R R' GI f j pc ra empty stk,
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_R_r ret RI G R GI f j pc ra empty stk -> lib_contract_x_R_r ret RI G' R' GI f j pc ra empty stk.
Proof using.
intros ret RI G G' R R' GI f j pc ra empty stk HG HRR H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT HR Hfrm HK.
apply (H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT (G_img_mono segs R R' mem HRR HR) Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HRI' & HGI').
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_R_r_mono (ret pl) G G' (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' HG Hp)
  | exact (conj HRI' HGI')].
Qed.

(* the post for r = 0 is the kit's lib_post_x_R *)
Lemma lib_post_x_R_of_r0 : forall G out stk L A regs mem md p n l T T' L' A' regs' mem' md',
lib_post_x_R_r 0 G out stk L A regs mem md p n l T T' L' A' regs' mem' md' ->
lib_post_x_R B API G out stk L A regs mem md p n l T T' L' A' regs' mem' md'.
Proof using.
intros G out stk L A regs mem md p n l T T' L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19).
rewrite H13 in H5.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
(conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 H19)))))))))))))))))).
Qed.

(* a contract for ret gives the kit's 0-only contract on the payloads where ret is 0 *)
Lemma lib_contract_x_R_of_r : forall ret RI G R GI f j pc ra empty stk,
lib_contract_x_R_r ret RI G R GI f j pc ra empty stk ->
lib_contract_x_R B API (fun pl j T A => RI pl j T A /\ ret pl = 0) G R GI f j pc ra empty stk.
Proof using.
intros ret RI G R GI f j pc ra empty stk H L A regs mem md p n pl T K Hpre [HRI H0] HGI HTL HpT HR Hfrm HK.
apply (H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HRI' & HGI').
rewrite H0 in Hp.
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
exact (conj (lib_post_x_R_of_r0 G (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' Hp)
  (conj (conj HRI' H0) HGI')).
Qed.

(* a contract for ret gives the contract for the constant return c on the payloads where ret is c *)
Lemma lib_contract_x_R_c_of_r : forall (c : Z) ret RI G R GI f j pc ra empty stk,
lib_contract_x_R_r ret RI G R GI f j pc ra empty stk ->
lib_contract_x_R_r (fun _ => c) (fun pl j T A => RI pl j T A /\ ret pl = c) G R GI f j pc ra empty stk.
Proof using.
intros c ret RI G R GI f j pc ra empty stk H L A regs mem md p n pl T K Hpre [HRI Hc0] HGI HTL HpT HR Hfrm HK.
apply (H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HRI' & HGI').
rewrite Hc0 in Hp.
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
exact (conj Hp (conj (conj HRI' Hc0) HGI')).
Qed.
End d.
End c.

Definition lib_contract_x_G_all_r {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_G_r fx rc LS B API SH SK ret G R GI f j pc ra empty stk.
Definition lib_contract_x_T_all_r {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte)
(pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_T_r fx rc LS B API SH SK ret G R GI f j pc ra empty stk.
Lemma lib_contract_x_T_all_r_of_G {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
lib_contract_x_G_all_r B API ret G R GI f pc ra empty stk ->
lib_contract_x_T_all_r B API ret G R (fun j T m => T = [] /\ GI j m) f pc ra empty stk.
Proof. intros H fx j Hj. exact (lib_contract_x_T_r_of_G B API ret G R GI f j pc ra empty stk (H fx j Hj)). Qed.
Definition lib_contract_x_R_all_r {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_R_r fx rc LS B API SH SK ret RI G R GI f j pc ra empty stk.
Lemma lib_contract_x_R_all_r_mono {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G G' R R' : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_R_all_r B API ret RI G R GI f pc ra empty stk -> lib_contract_x_R_all_r B API ret RI G' R' GI f pc ra empty stk.
Proof.
intros HG HRR H fx j Hj. exact (lib_contract_x_R_r_mono B API ret RI G G' R R' GI f j pc ra empty stk HG HRR (H fx j Hj)).
Qed.
Lemma lib_contract_x_R_all_r_of_T {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
(forall j, (j < 4)%nat -> forall pl T A m, RI pl j T A -> GI j T m -> exists b, res_ok_slots A b /\
@lib_room LS b (Z.of_nat (length pl)) /\
forall T' A' m', res_ok_slots A' (TD T T' (@lib_delta LS (Z.of_nat (length pl)) b)) -> GI (S j) T' m' -> RI pl (S j) T' A') ->
lib_contract_x_T_all_r B API ret G R GI f pc ra empty stk -> lib_contract_x_R_all_r B API ret RI G R GI f pc ra empty stk.
Proof. intros HRI H fx j Hj. exact (lib_contract_x_R_r_of_T B API ret RI G R GI f j pc ra empty stk (HRI j Hj) (H fx j Hj)). Qed.
Lemma lib_contract_x_R_all_of_r {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (ret : list byte -> Z)
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
lib_contract_x_R_all_r B API ret RI G R GI f pc ra empty stk ->
lib_contract_x_R_all B API (fun pl j T A => RI pl j T A /\ ret pl = 0) G R GI f pc ra empty stk.
Proof. intros H fx j Hj. exact (lib_contract_x_R_of_r B API ret RI G R GI f j pc ra empty stk (H fx j Hj)). Qed.
Lemma lib_contract_x_R_all_c_of_r {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B)
{SH : sink_head} {SK : sink_syms} (c : Z) (ret : list byte -> Z)
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
lib_contract_x_R_all_r B API ret RI G R GI f pc ra empty stk ->
lib_contract_x_R_all_r B API (fun _ => c) (fun pl j T A => RI pl j T A /\ ret pl = c) G R GI f pc ra empty stk.
Proof. intros H fx j Hj. exact (lib_contract_x_R_c_of_r B API c ret RI G R GI f j pc ra empty stk (H fx j Hj)). Qed.

(* The call site (Reusable/YL05.v lib_post_state, Reusable/YL06.v), for the return value r. *)
Definition lib_post_state_r (ra_lib r : Z) (ss : sstate) (k : nat) (rs2 : smem) : sstate :=
mkSS ra_lib (sr_set (sr_sets (ss_regs ss) (junk_upd k caller_saved)) 10%bv (SLit (r mod 2 ^ 64))) rs2 None (ss_facts ss).

Lemma lib_post_state_r_0 : forall ra_lib ss k rs2, lib_post_state_r ra_lib 0 ss k rs2 = lib_post_state ra_lib ss k rs2.
Proof. reflexivity. Qed.

Section c2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section e.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let MR := aa_MR API.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Variables (ra_lib stk : Z).

(* YL06.v lib_post_T, with a0 = r *)
Definition lib_post_T_r (r : Z) (G : list (Z * Z)) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p : Z) (T : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T ->
exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a).

Lemma lib_post_T_r_of_x_R_r : forall r G out L A regs mem md p n l T T' L' A' regs' mem' md',
lib_post_x_R_r B API r G out stk L A regs mem md p n l T T' L' A' regs' mem' md' ->
exists fds' pins', lib_post_T_r r G L A regs mem (md_rebase md fds' (ll_fs l) pins') p T L' A' regs' mem' md'.
Proof using.
intros r G out L A regs mem md p n l T T' L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & (vm' & fds' & pins' & Hmd & Hfds) & H8 & H9 & H10 & H11 & H12 & H13 & _).
rewrite H13 in H5.
exists fds', pins'. unfold lib_post_T_r. repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); exact H12].
exists vm'. rewrite Hmd. unfold md_rebase. rewrite with_vmmaps_os_upd, os_upd_twice. reflexivity.
Qed.

Lemma lib_post_frame_T_r :
forall r G L A regs mem md p T L' A' regs' mem' md' (E : env) sp_off keep (blks : list (nat * Z)),
lib_post_T_r r G L A regs mem md p T L' A' regs' mem' md' ->
keep_check B keep = true -> keep_avoid G keep = true ->
errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + stk <= bv_unsigned (getr regs 2) ->
(forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\
ptr_addr L q <> p /\ ~ In (ptr_addr L q, sz) T) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 -> ~ (bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off -> writable_at segs mem' a) /\
(forall a, in_ivl keep a = true ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a -> writable_at segs mem' a)) /\
(forall a, in_ivl [(errno_addr B, errno_addr B + 4)] a = true -> writable_at segs mem' a) /\
(forall n sz i, In (n, sz) blks -> 0 <= i < sz ->
mbyte segs mem' (bv_unsigned (ew E n) + i) = mbyte segs mem (bv_unsigned (ew E n) + i) /\
writable_at segs mem' (bv_unsigned (ew E n) + i)).
Proof using.
intros r G L A regs mem md p T L' A' regs' mem' md' E sp_off keep blks HP Hkc Hka Herr Hsp Hsplo Hblks.
destruct HP as (HMR' & HW' & HB' & Hid' & Ha0 & Hregs & Hvm & Hstab & Hfr & Hfri & Hbk & Hscr).
split; [| split; [| split; [| split]]].
- intros a Ha Ha64 Hns.
destruct (Hfr a) as [H1 H2].
+ exact (conj Ha Ha64).
+ unfold lib_scratch, spZ. rewrite Hsp. intros [Hs|Hs]; lia.
+ split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. apply Hscr. unfold lib_scratch, spZ. rewrite Hsp. left. exact Ha.
- intros a Ha. destruct (keep_check_sound B keep a Hkc Ha) as (Himg & Hlow & Hst & Hctx & Herrno).
destruct (Hfri a Himg Hst Hctx Herrno (keep_avoid_sound G keep a Hka Ha)) as [H1 H2].
split; [exact H1 | intros W; apply H2; exact W].
- intros a Ha. destruct (in_ivl_In _ a Ha) as (q & Hq & Haq). destruct Hq as [<-|[]]. cbn [fst snd] in Haq.
apply Hscr. unfold lib_scratch. right. exact Haq.
- intros n sz i Hin Hi. destruct (Hblks n sz Hin) as (q & HinA & Hq & Hqp & HqT). rewrite <- Hq. split.
+ apply (Hbk q sz i HinA HqT Hqp Hi).
+ apply present_writable. destruct (Hstab q sz HinA HqT) as (q' & HinA' & Hstab'). rewrite <- Hstab'.
exact (proj1 (mr_blocks B MR LAWS L' A' mem' md' q' sz i HMR' HinA' Hi)).
Qed.

Theorem st_ok_after_lib_T_r :
forall r G k E ss regs pc mem md p T L A L' A' regs' mem' md' (sp_off : Z) keep
(blks : list (nat * Z)) (l1 : list (nat * YP09.region)),
st_ok segs E ss (mkst regs pc mem (seg_rom segs)) -> stack_anchored E (ss_facts ss) ->
ss_atoms_lt k ss = true ->
lib_post_T_r r G L A regs mem md p T L' A' regs' mem' md' ->
keep_check B keep = true -> keep_avoid G keep = true -> errno_addr B + 4 <= alloc_ceiling ->
bv_unsigned (getr regs 2) = bv_unsigned (ew E 0) + sp_off ->
alloc_ceiling + stk <= bv_unsigned (getr regs 2) ->
(forall n sz, In (n, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E n) /\
ptr_addr L q <> p /\ ~ In (ptr_addr L q, sz) T) ->
relayout_ok segs (ss_mem ss) l1 = true ->
mem_atoms_lt k (map snd l1) = true ->
call_frame_check (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks (map snd l1) = true ->
sr_get (ss_regs ss) 1 = SLit ra_lib ->
st_ok segs (havoc E k (map (getr regs') caller_saved))
(lib_post_state_r ra_lib r ss k (map snd l1))
(mkst regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)).
Proof using.
intros r G k E ss regs pc mem md p T L A L' A' regs' mem' md' sp_off keep blks l1
HS HSA Hat HP Hkc Hka Herr Hsp Hsplo Hblks Hrl Hma Hcf Hra.
assert (HS1 : st_ok segs (havoc E k (map (getr regs') caller_saved))
(mkSS ra_lib (sr_sets (ss_regs ss) (junk_upd k caller_saved)) (map snd l1) None (ss_facts ss))
(mkst regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs))).
{ change (junk_upd k caller_saved) with ([] ++ junk_upd k caller_saved).
eapply (st_ok_splice_havoc segs k E ss regs regs' pc ra_lib mem mem' (map snd l1) [] caller_saved HS Hat).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- exact Hma.
- cbn [map fst app]. apply regs_preserved_frame. destruct HP as (_ & _ & _ & _ & _ & Hregs & _). exact Hregs.
- constructor.
- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & HG). cbn [ms_mem mkst] in HM.
destruct (lib_post_frame_T_r r G L A regs mem md p T L' A' regs' mem' md' E sp_off keep blks
HP Hkc Hka Herr Hsp Hsplo Hblks) as (F1 & F2 & F3 & F5 & F4).
apply (mem_ok_call_frame segs (ss_facts ss) sp_off stk keep [(errno_addr B, errno_addr B + 4)] blks E mem mem' F1 F2 F3 F5 F4 HG HSA).
+ eapply mem_ok_relayout; [exact HM | exact Hrl].
+ exact Hcf. }
unfold lib_post_state_r. apply (st_ok_regs segs _ _ _ _ HS1).
cbn [ss_regs]. intros r'. destruct (decide (r' = 10%bv)) as [->|Hne].
- rewrite sr_get_set_same by reflexivity.
destruct HS1 as (_ & _ & _ & _ & _ & _ & Hregs1 & _). rewrite <- (Hregs1 10%bv). cbn [ms_regs mkst].
destruct HP as (_ & _ & _ & _ & Ha0 & _). rewrite Ha0.
first [ exact (Z_to_bv64_mod r) | exact (eq_sym (Z_to_bv64_mod r)) ].
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End e.

Section d2.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Let LAWS := aa_laws API.
Context {SH : sink_head} {SK : sink_syms}.
Variables (pc_lib ra_lib empty stk : Z).
Variable G : list (Z * Z).
Variable R : list (Z * Z).
Variable GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop.
Variable RI : list byte -> nat -> list (Z * Z) -> astate -> Prop.
Variable OUT : list byte -> list byte.
Variable ret : list byte -> Z.
Hypothesis LIBX : lib_contract_x_R_all_r B API ret RI G R GI OUT pc_lib ra_lib empty stk.
Hypothesis Hstk : 0 <= stk.
Hypothesis Hfrm : frm_zero fp_csr.

(* YL06.v lib_site_x_R: the continuation gets the state with a0 = ret pl and the leaf with ll_ret l = ret pl *)
Theorem lib_site_x_R_r : forall j T E ss ms md L A p n pl sp_off keep blks k l1 rs2 (K : lleaf -> TSet),
(j < 4)%nat ->
st_ok segs E ss ms -> stack_anchored E (ss_facts ss) ->
lib_site_check B pc_lib ra_lib stk ss sp_off keep blks k l1 = true ->
keep_avoid G keep = true ->
drv_add_statics B (map snd l1) (k + 16) = Some rs2 ->
MR L A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
GI j T (ms_mem ms) -> tb_live L A T -> (0 < n -> ~ In (p, n) T) ->
G_img segs R (ms_mem ms) ->
fdchan (Z_to_bv 64 2) ch_stderr md ->
getr (ms_regs ms) 10%bv = Z_to_bv 64 p -> getr (ms_regs ms) 11%bv = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ exists q, In (q, n) (user_blocks A) /\ ptr_addr L q = p)) ->
(forall kb sz, In (kb, sz) blks -> exists q, In (q, sz) (user_blocks A) /\ ptr_addr L q = bv_unsigned (ew E kb) /\
ptr_addr L q <> p /\ ~ In (ptr_addr L q, sz) T) ->
n = Z.of_nat (length pl) -> blk_data B (ms_mem ms) p pl ->
RI pl j T A ->
sink_none B (ms_mem ms) md -> fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Fs.fs_sorted (m_fs md) = true ->
bv_unsigned (ew E 0) + sp_off <= 2 ^ 47 ->
(forall (l : lleaf) (fx' : FPState) A' L' ms' md' g T',
@st_ok segs fx' (post_env E k (ms_regs ms') g) (mkSS ra_lib (ss_regs (lib_post_state_r ra_lib (ret pl) ss k rs2)) rs2 None (ss_facts ss)) ms' ->
stack_anchored (post_env E k (ms_regs ms') g) (ss_facts ss) ->
frm_zero (@fp_csr fx') ->
MR L' A' (ms_mem ms') md' -> WF A' -> bounded A' -> st_init_done A' = true ->
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) ->
(forall q sz, In (q, sz) (user_blocks A) -> ~ In (ptr_addr L q, sz) T ->
exists q', In (q', sz) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) ->
(forall a, alloc_ceiling <= a -> a < 2 ^ 64 ->
~ (bv_unsigned (ew E 0) + sp_off - stk <= a < bv_unsigned (ew E 0) + sp_off) ->
mbyte segs (ms_mem ms') a = mbyte segs (ms_mem ms) a) ->
(forall q sz i, In (q, sz) (user_blocks A) -> ~ In (ptr_addr L q, sz) T -> ptr_addr L q <> p -> 0 <= i < sz ->
mbyte segs (ms_mem ms') (ptr_addr L q + i) = mbyte segs (ms_mem ms) (ptr_addr L q + i)) ->
ll_ret l = ret pl -> ll_out l = OUT pl -> Fs.fs_sorted (ll_fs l) = true ->
sink_none B (ms_mem ms') md' -> RI pl (S j) T' A' ->
(forall i, 0 <= i < n -> mbyte segs (ms_mem ms') (p + i) = mbyte segs (ms_mem ms) (p + i)) ->
tb_live L' A' T' -> (forall t, In t T' -> In t (blocks L A) -> In t T) ->
GI (S j) T' (ms_mem ms') ->
realizes segs (mkCfg ms' md') (K l)) ->
realizes segs (mkCfg ms md) (LIBK pl (m_fs md) K).
Proof using AX LIBX Hstk Hfrm.
intros j T E ss ms md L A p n pl sp_off keep blks k l1 rs2 K Hj HS HSA Hck Hka Hrs2 HMR HW HB Hid HGI HTL HpT HR Hfd Hp Hn Hpn Hblks
Hlen Hpl HRI HSN Hfree Hsorted Htop HK.
destruct (lib_site_check_sound B pc_lib ra_lib stk _ _ _ _ _ _ Hck) as (Hpc & Hrv & Hcp & Hkc & Herr & Hrl & Hat & Hma & Hat2 & Hcf & Hra).
pose proof (st_ok_mkst segs E ss ms HS Hrv) as Hshape.
destruct (lib_pre_intro B API ra_lib empty stk Hstk E ss ms L A md sp_off p n HS HSA HMR HW HB Hid Hcp Hp Hn Hpn) as (Hpre & Hsp & Hsplo).
rewrite Hshape in HS |- *. rewrite Hpc in HS |- *. cbn [ms_regs ms_mem mkst] in *.
assert (Hprew : lib_pre_w B API stk empty L A (ms_regs ms) (ms_mem ms) md ra_lib p n pl).
{ split; [exact Hpre|]. split; [exact Hlen|]. split; [exact Hpl|].
split; [exact HSN|]. split; [exact Hfree|]. split; [exact Hsorted|]. split; [exact Hfd|]. unfold spZ. rewrite Hsp. exact Htop. }
apply (LIBX fx j Hj L A (ms_regs ms) (ms_mem ms) md p n pl T K Hprew HRI HGI HTL HpT HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & -> & Hfrm' & Hpostx & HRI' & HGI').
pose proof Hpostx as (HMR' & HW' & HB' & Hid' & Ha0 & Hregs & Hvm & Hstab & Hfr & Hfri & Hbk & Hscr & Hret & Hout & Hsorted' & HSN' &
Hplk & HTL' & HTT).
destruct (lib_post_T_r_of_x_R_r B API stk (ret pl) G (OUT pl) L A (ms_regs ms) (ms_mem ms) md p n l T T' L' A' regs' mem' md' Hpostx)
  as (fds1 & pins1 & Hpost).
assert (HS1 := st_ok_after_lib_T_r B API ra_lib stk (ret pl) G k E ss (ms_regs ms) _ (ms_mem ms) (md_rebase md fds1 (ll_fs l) pins1) p T L A L' A' regs' mem' md'
sp_off keep blks l1 HS HSA Hat Hpost Hkc Hka Herr Hsp Hsplo Hblks Hrl Hma Hcf Hra).
unfold drv_add_statics in Hrs2.
destruct (abs_region_index (map snd l1) (ms_got_guard B) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_libc B + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd l1) (ms_guard B) 0) as [i3|]; [|discriminate].
assert (Hat3 : ss_atoms_lt (k + 16) (lib_post_state_r ra_lib (ret pl) ss k (map snd l1)) = true).
{ unfold lib_post_state_r. unfold ss_atoms_lt in Hat2 |- *. cbn [ss_regs ss_mem ss_facts ss_resv] in Hat2 |- *.
apply andb_prop in Hat2 as [Hat2 _]. apply andb_prop in Hat2 as [Hat2 HF']. apply andb_prop in Hat2 as [HR' HM'].
rewrite (regs_atoms_lt_set (k + 16) _ 10%bv (SLit (ret pl mod 2 ^ 64)) HR' eq_refl), HM', HF'. reflexivity. }
apply (st_ok_xfx fx fx') in HS1.
destruct (st_ok_statics B MR AX _ _ (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) L' A' md' (k + 16) i1 i2 i3 rs2
HS1 HMR' Hat3 Hrs2) as (g & Hg01 & HS2).
apply (HK l fx' A' L' (@mkst fx' regs' (Z_to_bv 64 ra_lib) mem' (seg_rom segs)) md' g T').
- exact HS2.
- apply (stack_anchored_agree_ss k E _ ss (post_env_agree E k regs' g) Hat HSA).
- exact Hfrm'.
- exact HMR'.
- exact HW'.
- exact HB'.
- exact Hid'.
- exact Hvm.
- exact Hstab.
- cbn [ms_mem mkst]. intros a Ha Ha64 Hns.
destruct (lib_post_frame_T_r B API stk (ret pl) G L A (ms_regs ms) (ms_mem ms) (md_rebase md fds1 (ll_fs l) pins1) p T L' A' regs' mem' md' E sp_off keep blks
Hpost Hkc Hka Herr Hsp Hsplo Hblks) as (F1 & _).
exact (proj1 (F1 a Ha Ha64 Hns)).
- cbn [ms_mem mkst]. exact Hbk.
- exact Hret.
- exact Hout.
- exact Hsorted'.
- exact HSN'.
- exact HRI'.
- cbn [ms_mem mkst]. exact Hplk.
- exact HTL'.
- exact HTT.
- exact HGI'.
Qed.
End d2.
End c2.
