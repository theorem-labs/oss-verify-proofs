(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0i.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0i YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import AllocSlots.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {AM : AllocMode}.
Definition G_local (segs : list Segment) (G : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) : Prop :=
forall j m m', (forall a, in_globals G a -> mbyte segs m' a = mbyte segs m a) -> GI j m -> GI j m'.
Definition G_img (segs : list Segment) (G : list (Z * Z)) (mem : word -> option byte) : Prop :=
forall a, in_globals G a -> mbyte segs mem a = seg_rom segs (Z_to_bv 64 a).
Lemma G_local_mono : forall segs G G' GI, (forall a, in_globals G a -> in_globals G' a) ->
G_local segs G GI -> G_local segs G' GI.
Proof using. intros segs G G' GI HG H j m m' Hm. apply H. intros a Ha. exact (Hm a (HG a Ha)). Qed.
Lemma G_img_mono : forall segs G G' mem, (forall a, in_globals G a -> in_globals G' a) ->
G_img segs G' mem -> G_img segs G mem.
Proof using. intros segs G G' mem HG H a Ha. exact (H a (HG a Ha)). Qed.
Lemma G_img_nil : forall segs mem, G_img segs [] mem.
Proof using. intros segs mem a Ha. destruct (in_globals_nil a Ha). Qed.
Definition in_tb (T : list (Z * Z)) (a : Z) : Prop :=
exists t k, In (t, k) T /\ t <= a < t + k.
Definition tb_live (L : layout) (A : astate) (T : list (Z * Z)) : Prop :=
NoDup T /\ forall t, In t T -> In t (blocks L A).
Lemma tb_live_nil : forall L A, tb_live L A [].
Proof using. intros L A. split; [constructor | intros t Ht; destruct Ht]. Qed.
Lemma notin_nil : forall x : Z * Z, ~ In x [].
Proof using. intros x H. exact H. Qed.
Lemma notin_n0 : forall (n p : Z) (T : list (Z * Z)), n = 0 -> 0 < n -> ~ In (p, n) T.
Proof using. intros n p T -> H. lia. Qed.
Lemma kept_notin : forall L A T T' q k X,
In (q, k) (user_blocks A) -> ptr_addr L q = X -> ~ In (X, k) T ->
(forall t, In t T' -> In t (blocks L A) -> In t T) -> ~ In (X, k) T'.
Proof using.
intros L A T T' q k X Hq HX HT HTT H. apply HT. apply HTT; [exact H|].
unfold blocks. rewrite <- HX. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hq).
Qed.
Definition G_local_T (segs : list Segment) (G : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) : Prop :=
forall j T m m', (forall a, in_globals G a \/ in_tb T a -> mbyte segs m' a = mbyte segs m a) -> GI j T m -> GI j T m'.
Lemma G_local_T_mono : forall segs G G' GI, (forall a, in_globals G a -> in_globals G' a) ->
G_local_T segs G GI -> G_local_T segs G' GI.
Proof using.
intros segs G G' GI HG H j T m m' Hm. apply H. intros a [Ha|Ha]; apply Hm; [left; exact (HG a Ha) | right; exact Ha].
Qed.
Lemma G_local_T_of_G : forall segs G GI, G_local segs G GI -> G_local_T segs G (fun j T m => T = [] /\ GI j m).
Proof using.
intros segs G GI H j T m m' Hm [HT HGI]. split; [exact HT|]. apply (H j m m'); [|exact HGI].
intros a Ha. apply Hm. left. exact Ha.
Qed.
Definition TD (T T' : list (Z * Z)) (b : sbound) : sbound :=
fold_left (fun b t => sb_malloc b (snd t)) T' (fold_left (fun b t => sb_free b (snd t)) T b).
Lemma TD_malloc_form : forall (T : list (Z * Z)) (b : sbound), fold_left (fun b t => sb_malloc b (snd t)) T b =
SB (sb_live b + Z.of_nat (length T)) (sb_bytes b + fold_right (fun t s => snd t + s) 0 T) (sb_cap b).
Proof using.
induction T as [|t T IH]; intros b; cbn [fold_left fold_right length].
- destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
- rewrite IH. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.
Lemma TD_free_form : forall (T : list (Z * Z)) (b : sbound), fold_left (fun b t => sb_free b (snd t)) T b =
SB (sb_live b - Z.of_nat (length T)) (sb_bytes b - fold_right (fun t s => snd t + s) 0 T) (sb_cap b).
Proof using.
induction T as [|t T IH]; intros b; cbn [fold_left fold_right length].
- destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
- rewrite IH. unfold sb_free. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.
Lemma TD_chain : forall T T' b, TD T T' (TD [] T b) = TD [] T' b.
Proof using.
intros T T' b. unfold TD. cbn [fold_left]. f_equal.
rewrite TD_free_form, TD_malloc_form. destruct b as [l y c]. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.
Definition run_RI (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (pl : list byte) (r : dleaf * astate) : Prop :=
match fst r with DL_run _ _ _ => RI pl 0%nat [] (snd r) | _ => True end.
Definition RI_G (pl : list byte) (j : nat) (T : list (Z * Z)) (A : astate) : Prop :=
exists b, res_ok_slots A b /\ room_calls (Z.of_nat (length pl)) (4 - j)%nat b.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Definition lib_pre_x (stk empty : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ra p n : Z) (pl : list byte) (b : sbound) : Prop :=
lib_pre B API stk empty L A regs mem md ra p n /\
n = Z.of_nat (length pl) /\ blk_data B mem p pl /\
res_ok_slots A b /\ lib_room b n /\
sink_none B mem md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
fdchan (Z_to_bv 64 2) ch_stderr md /\
spZ regs <= 2 ^ 47.
Lemma lib_pre_x_sp : forall stk empty L A regs mem md ra p n pl b,
lib_pre_x stk empty L A regs mem md ra p n pl b -> spZ regs <= TASK_SIZE.
Proof using.
intros stk empty L A regs mem md ra p n pl b H. unfold lib_pre_x in H.
repeat match type of H with _ /\ ?R => destruct H as [_ H] end. unfold TASK_SIZE. lia.
Qed.
Definition lib_post_x (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok_slots A' (lib_delta n b) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).
Definition lib_contract_x (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b (K : lleaf -> TSet),
lib_pre_x stk empty L A regs mem md ra p n pl b ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x stk L A regs mem md p n b l L' A' regs' mem' md') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
Definition md_rebase (md : Model) (fds' : _) (fs' : Fs) (pins' : _) : Model := os_upd (m_vmmaps md) fds' fs' pins' md.
Definition lib_post_x_G (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
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
ll_ret l = 0 /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok_slots A' (lib_delta n b) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).
Definition lib_contract_x_G (G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte)
(j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b (K : lleaf -> TSet),
lib_pre_x stk empty L A regs mem md ra p n pl b ->
GI j mem ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_G G (f pl) stk L A regs mem md p n b l L' A' regs' mem' md' /\
GI (S j) mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
Lemma lib_post_of_x_G : forall G out stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x_G G out stk L A regs mem md p n b l L' A' regs' mem' md' ->
exists fds' pins', lib_post B API G stk L A regs mem (md_rebase md fds' (ll_fs l) pins') p L' A' regs' mem' md'.
Proof using.
intros G out stk L A regs mem md p n b l L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & (vm' & fds' & pins' & Hmd & Hfds) & H8 & H9 & H10 & H11 & H12 & _).
exists fds', pins'. unfold lib_post. repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); exact H12].
exists vm'. rewrite Hmd. unfold md_rebase. rewrite with_vmmaps_os_upd, os_upd_twice. reflexivity.
Qed.
Lemma lib_post_x_G_of_x : forall G stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x stk L A regs mem md p n b l L' A' regs' mem' md' ->
lib_post_x_G G [] stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
intros G stk L A regs mem md p n b l L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
repeat (split; [assumption|]). split; [intros a Ha Hs Hc He _; exact (H10 a Ha Hs Hc He) | exact H11].
Qed.
Lemma lib_post_x_G_mono : forall G G' out stk L A regs mem md p n b l L' A' regs' mem' md',
(forall a, in_globals G a -> in_globals G' a) ->
lib_post_x_G G out stk L A regs mem md p n b l L' A' regs' mem' md' ->
lib_post_x_G G' out stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
intros G G' out stk L A regs mem md p n b l L' A' regs' mem' md' HG (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
repeat (split; [assumption|]).
split; [intros a Ha Hs Hc He Hg; exact (H10 a Ha Hs Hc He (fun h => Hg (HG a h))) | exact H11].
Qed.
Lemma lib_post_x_of_G_nil : forall stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x_G [] [] stk L A regs mem md p n b l L' A' regs' mem' md' ->
lib_post_x stk L A regs mem md p n b l L' A' regs' mem' md'.
Proof using.
intros stk L A regs mem md p n b l L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
repeat (split; [assumption|]).
split; [intros a Ha Hs Hc He; exact (H10 a Ha Hs Hc He (in_globals_nil a)) | exact H11].
Qed.
Lemma lib_contract_x_G_of_x : forall G R j pc ra empty stk,
lib_contract_x pc ra empty stk -> lib_contract_x_G G R (fun _ _ => True) (fun _ => []) j pc ra empty stk.
Proof using.
intros G R j pc ra empty stk H L A regs mem md p n pl b K Hpre _ _ Hfrm HK.
apply (H L A regs mem md p n pl b K Hpre Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp).
apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_G_of_x G stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | exact I].
Qed.
Lemma lib_contract_x_of_G_nil : forall j pc ra empty stk,
lib_contract_x_G [] [] (fun _ _ => True) (fun _ => []) j pc ra empty stk -> lib_contract_x pc ra empty stk.
Proof using.
intros j pc ra empty stk H L A regs mem md p n pl b K Hpre Hfrm HK.
apply (H L A regs mem md p n pl b K Hpre I (G_img_nil segs mem) Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & _).
apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
exact (lib_post_x_of_G_nil stk L A regs mem md p n b l L' A' regs' mem' md' Hp).
Qed.
Lemma lib_contract_x_G_mono : forall G G' R R' GI f j pc ra empty stk,
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_G G R GI f j pc ra empty stk -> lib_contract_x_G G' R' GI f j pc ra empty stk.
Proof using.
intros G G' R R' GI f j pc ra empty stk HG HRR H L A regs mem md p n pl b K Hpre HGI HR Hfrm HK.
apply (H L A regs mem md p n pl b K Hpre HGI (G_img_mono segs R R' mem HRR HR) Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
apply HK. exists fx', L', A', regs', mem', md'. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_G_mono G G' (f pl) stk L A regs mem md p n b l L' A' regs' mem' md' HG Hp) | exact HGI'].
Qed.
Definition lib_post_x_T (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf) (T T' : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
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
ll_ret l = 0 /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok_slots A' (TD T T' (lib_delta n b)) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
tb_live L' A' T' /\
(forall t, In t T' -> In t (blocks L A) -> In t T).
Definition lib_contract_x_T (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b T (K : lleaf -> TSet),
lib_pre_x stk empty L A regs mem md ra p n pl b ->
GI j T mem ->
tb_live L A T ->
(0 < n -> ~ In (p, n) T) ->
G_img segs R mem ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md' T',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x_T G (f pl) stk L A regs mem md p n b l T T' L' A' regs' mem' md' /\
GI (S j) T' mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
Lemma lib_post_x_T_of_G : forall G out stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x_G G out stk L A regs mem md p n b l L' A' regs' mem' md' ->
lib_post_x_T G out stk L A regs mem md p n b l [] [] L' A' regs' mem' md'.
Proof using.
intros G out stk L A regs mem md p n b l L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj (fun q k Hq _ => H8 q k Hq)
(conj H9 (conj H10 (conj (fun q k i Hq _ => H11 q k i Hq) (conj H12 (conj H13 (conj H14 (conj H15 (conj H16
(conj H17 (conj H18 (conj (tb_live_nil L' A') _))))))))))))))))))).
intros t Ht. destruct Ht.
Qed.
Lemma lib_contract_x_T_of_G : forall G R GI f j pc ra empty stk,
lib_contract_x_G G R GI f j pc ra empty stk ->
lib_contract_x_T G R (fun j T m => T = [] /\ GI j m) f j pc ra empty stk.
Proof using.
intros G R GI f j pc ra empty stk H L A regs mem md p n pl b T K Hpre [HT HGI] _ _ HR Hfrm HK.
subst T.
apply (H L A regs mem md p n pl b K Hpre HGI HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & HGI').
apply HK. exists fx', L', A', regs', mem', md', []. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_T_of_G G (f pl) stk L A regs mem md p n b l L' A' regs' mem' md' Hp) | split; [reflexivity | exact HGI']].
Qed.
Definition lib_pre_w (stk empty : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ra p n : Z) (pl : list byte) : Prop :=
lib_pre B API stk empty L A regs mem md ra p n /\
n = Z.of_nat (length pl) /\ blk_data B mem p pl /\
sink_none B mem md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
fdchan (Z_to_bv 64 2) ch_stderr md /\
spZ regs <= 2 ^ 47.
Lemma lib_pre_x_of_w : forall stk empty L A regs mem md ra p n pl b,
lib_pre_w stk empty L A regs mem md ra p n pl -> res_ok_slots A b -> lib_room b n ->
lib_pre_x stk empty L A regs mem md ra p n pl b.
Proof using.
intros stk empty L A regs mem md ra p n pl b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) Hb Hr.
exact (conj H1 (conj H2 (conj H3 (conj Hb (conj Hr (conj H4 (conj H5 (conj H6 (conj H7 H8))))))))).
Qed.
Definition lib_post_x_R (G : list (Z * Z)) (out : list byte) (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (l : lleaf) (T T' : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
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
ll_ret l = 0 /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
tb_live L' A' T' /\
(forall t, In t T' -> In t (blocks L A) -> In t T).
Definition lib_contract_x_R (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z))
(GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (j : nat) (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl T (K : lleaf -> TSet),
lib_pre_w stk empty L A regs mem md ra p n pl ->
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
lib_post_x_R G (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' /\
RI pl (S j) T' A' /\
GI (S j) T' mem') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
Lemma lib_post_x_R_of_T : forall G out stk L A regs mem md p n b l T T' L' A' regs' mem' md',
lib_post_x_T G out stk L A regs mem md p n b l T T' L' A' regs' mem' md' ->
lib_post_x_R G out stk L A regs mem md p n l T T' L' A' regs' mem' md' /\ res_ok_slots A' (TD T T' (lib_delta n b)).
Proof using.
intros G out stk L A regs mem md p n b l T T' L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20).
split; [|exact H17].
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
(conj H13 (conj H14 (conj H15 (conj H16 (conj H18 (conj H19 H20)))))))))))))))))).
Qed.
Lemma lib_contract_x_R_of_T : forall (RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) G R GI f j pc ra empty stk,
(forall pl T A m, RI pl j T A -> GI j T m -> exists b, res_ok_slots A b /\ lib_room b (Z.of_nat (length pl)) /\
forall T' A' m', res_ok_slots A' (TD T T' (lib_delta (Z.of_nat (length pl)) b)) -> GI (S j) T' m' -> RI pl (S j) T' A') ->
lib_contract_x_T G R GI f j pc ra empty stk -> lib_contract_x_R RI G R GI f j pc ra empty stk.
Proof using.
intros RI G R GI f j pc ra empty stk HRI H L A regs mem md p n pl T K Hpre HR0 HGI HTL HpT HR Hfrm HK.
pose proof Hpre as (_ & Hn & _).
destruct (HRI pl T A mem HR0 HGI) as (b & Hb & Hroom & Hnext). rewrite <- Hn in Hroom, Hnext.
apply (H L A regs mem md p n pl b T K (lib_pre_x_of_w stk empty L A regs mem md ra p n pl b Hpre Hb Hroom) HGI HTL HpT HR Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HGI').
destruct (lib_post_x_R_of_T G (f pl) stk L A regs mem md p n b l T T' L' A' regs' mem' md' Hp) as [Hp' Hres].
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
exact (conj Hp' (conj (Hnext T' A' mem' Hres HGI') HGI')).
Qed.
Lemma lib_post_x_R_mono : forall G G' out stk L A regs mem md p n l T T' L' A' regs' mem' md',
(forall a, in_globals G a -> in_globals G' a) ->
lib_post_x_R G out stk L A regs mem md p n l T T' L' A' regs' mem' md' ->
lib_post_x_R G' out stk L A regs mem md p n l T T' L' A' regs' mem' md'.
Proof using.
intros G G' out stk L A regs mem md p n l T T' L' A' regs' mem' md' HG
(H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ H11)))))))))).
intros a Ha Hs Hc He Hg. exact (H10 a Ha Hs Hc He (fun h => Hg (HG a h))).
Qed.
Lemma lib_contract_x_R_mono : forall RI G G' R R' GI f j pc ra empty stk,
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_R RI G R GI f j pc ra empty stk -> lib_contract_x_R RI G' R' GI f j pc ra empty stk.
Proof using.
intros RI G G' R R' GI f j pc ra empty stk HG HRR H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT HR Hfrm HK.
apply (H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT (G_img_mono segs R R' mem HRR HR) Hfrm).
intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HRI' & HGI').
apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
split; [exact (lib_post_x_R_mono G G' (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' HG Hp) | exact (conj HRI' HGI')].
Qed.
Lemma MR_rebase : MR_laws B MR -> forall L A mem md fds' fs' pins', MR L A mem md -> MR L A mem (md_rebase md fds' fs' pins').
Proof.
intros LAWS L A mem md fds' fs' pins' H. destruct (mr_model B MR LAWS _ _ _ _ H) as (Hh & Hlz & Hmat).
apply (mr_frame B MR LAWS L A mem mem md (md_rebase md fds' fs' pins') H); auto.
intros p n i Hin Hi. exact (proj1 (mr_blocks B MR LAWS L A mem md p n i H Hin Hi)).
Qed.
End d.
End c.
Section e.
Context {AM : AllocMode}.
Definition lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(pc ra empty stk : Z) : Prop :=
forall fx : FPState, @lib_contract_x fx rc LS AM B API SH SK pc ra empty stk.
Definition lib_contract_x_G_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_G fx rc LS AM B API SH SK G R GI f j pc ra empty stk.
Lemma lib_contract_x_G_all_of_x {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(G R : list (Z * Z)) (pc ra empty stk : Z) :
lib_contract_x_all B API pc ra empty stk -> lib_contract_x_G_all B API G R (fun _ _ => True) (fun _ => []) pc ra empty stk.
Proof. intros H fx j _. exact (lib_contract_x_G_of_x B API G R j pc ra empty stk (H fx)). Qed.
Theorem lib_contract_x_G_all_nil {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(pc ra empty stk : Z) :
lib_contract_x_G_all B API [] [] (fun _ _ => True) (fun _ => []) pc ra empty stk <-> lib_contract_x_all B API pc ra empty stk.
Proof.
split.
- intros H fx. exact (lib_contract_x_of_G_nil B API 0%nat pc ra empty stk (H fx 0%nat (Nat.lt_0_succ 3))).
- exact (lib_contract_x_G_all_of_x B API [] [] pc ra empty stk).
Qed.
Lemma lib_contract_x_G_all_mono {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(G G' R R' : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_G_all B API G R GI f pc ra empty stk -> lib_contract_x_G_all B API G' R' GI f pc ra empty stk.
Proof. intros HG HRR H fx j Hj. exact (lib_contract_x_G_mono B API G G' R R' GI f j pc ra empty stk HG HRR (H fx j Hj)). Qed.
Lemma G_local_True : forall segs G, G_local segs G (fun _ _ => True).
Proof. intros segs G j m m' _ H. exact H. Qed.
Definition lib_contract_x_T_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_T fx rc LS AM B API SH SK G R GI f j pc ra empty stk.
Lemma lib_contract_x_T_all_of_G {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(G R : list (Z * Z)) (GI : nat -> (word -> option byte) -> Prop) (f : list byte -> list byte) (pc ra empty stk : Z) :
lib_contract_x_G_all B API G R GI f pc ra empty stk ->
lib_contract_x_T_all B API G R (fun j T m => T = [] /\ GI j m) f pc ra empty stk.
Proof. intros H fx j Hj. exact (lib_contract_x_T_of_G B API G R GI f j pc ra empty stk (H fx j Hj)). Qed.
Definition lib_contract_x_R_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (pc ra empty stk : Z) : Prop :=
forall (fx : FPState) (j : nat), (j < 4)%nat -> @lib_contract_x_R fx rc LS AM B API SH SK RI G R GI f j pc ra empty stk.
Lemma lib_contract_x_R_all_mono {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G G' R R' : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (pc ra empty stk : Z) :
(forall a, in_globals G a -> in_globals G' a) ->
(forall a, in_globals R a -> in_globals R' a) ->
lib_contract_x_R_all B API RI G R GI f pc ra empty stk -> lib_contract_x_R_all B API RI G' R' GI f pc ra empty stk.
Proof. intros HG HRR H fx j Hj. exact (lib_contract_x_R_mono B API RI G G' R R' GI f j pc ra empty stk HG HRR (H fx j Hj)). Qed.
Lemma lib_contract_x_R_all_of_T {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(RI : list byte -> nat -> list (Z * Z) -> astate -> Prop) (G R : list (Z * Z)) (GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop)
(f : list byte -> list byte) (pc ra empty stk : Z) :
(forall j, (j < 4)%nat -> forall pl T A m, RI pl j T A -> GI j T m -> exists b, res_ok_slots A b /\ @lib_room LS b (Z.of_nat (length pl)) /\
forall T' A' m', res_ok_slots A' (TD T T' (@lib_delta LS (Z.of_nat (length pl)) b)) -> GI (S j) T' m' -> RI pl (S j) T' A') ->
lib_contract_x_T_all B API G R GI f pc ra empty stk -> lib_contract_x_R_all B API RI G R GI f pc ra empty stk.
Proof. intros HRI H fx j Hj. exact (lib_contract_x_R_of_T B API RI G R GI f j pc ra empty stk (HRI j Hj) (H fx j Hj)). Qed.
End e.
Lemma RI_G_step {LS : lib_shape} (GI : nat -> (word -> option byte) -> Prop) : forall j, (j < 4)%nat ->
forall pl T A m, RI_G pl j T A -> (T = [] /\ GI j m) -> exists b, res_ok_slots A b /\ lib_room b (Z.of_nat (length pl)) /\
forall T' A' m', res_ok_slots A' (TD T T' (lib_delta (Z.of_nat (length pl)) b)) -> (T' = [] /\ GI (S j) m') -> RI_G pl (S j) T' A'.
Proof.
intros j Hj pl T A m (b & Hb & Hr) [-> _].
replace (4 - j)%nat with (S (3 - j)) in Hr by lia. destruct Hr as [Hr1 Hr2].
exists b. split; [exact Hb|]. split; [exact Hr1|].
intros T' A' m' Hb' [-> _]. exists (lib_delta (Z.of_nat (length pl)) b). split; [exact Hb'|].
replace (4 - S j)%nat with (3 - j)%nat by lia. exact Hr2.
Qed.
