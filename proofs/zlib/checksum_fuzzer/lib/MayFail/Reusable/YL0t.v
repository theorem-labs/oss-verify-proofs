(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YL0t.v, with its module paths changed; 2 of its 183 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac drv_bd AX keep E HS HF HMR HD Hin :=
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
let G := lazymatch type of HS with st_ok _ _ ?ss' _ => constr:(ss_facts ss') | st_ok_ecall _ _ ?ss' _ => constr:(ss_facts ss') end in
lazymatch type of HD with blk_data _ _ ?a ?bs =>
let HD' := fresh "HDx" in
pose proof (blk_data_after_frame _ _ (aa_laws _) AX _ _ m0 m1 _ E G keep rs0 _ _ a bs HMR
ltac:(lazymatch type of HS with
| st_ok _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X
| st_ok_ecall _ _ _ _ => destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X end)
ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin) as HD';
specialize (HD' ltac:(lia) ltac:(lia) HD); clear HD; rename HD' into HD
end end.
Definition env_top (E : env) : Prop := bv_unsigned (ew E 0) <= 2 ^ 47.
Lemma env_top_agree : forall k E E', (1 <= k)%nat -> env_agree k E E' -> env_top E -> env_top E'.
Proof. intros k E E' Hk [HA _] H. unfold env_top. rewrite HA by lia. exact H. Qed.
Lemma env_top_havoc : forall E k ws, (1 <= k)%nat -> env_top E -> env_top (havoc E k ws).
Proof. intros E k ws Hk H. eapply env_top_agree; [exact Hk | apply env_agree_havoc | exact H]. Qed.
Lemma env_top_post : forall E k regs g, (1 <= k)%nat -> env_top E -> env_top (post_env E k regs g).
Proof. intros E k regs g Hk H. eapply env_top_agree; [exact Hk | apply post_env_agree | exact H]. Qed.
Lemma env_top_ewset : forall E n v, (n <> 0)%nat -> env_top E -> env_top (ewset E n v).
Proof. intros E n v Hn H. unfold env_top. rewrite ew_ewset_other by lia. exact H. Qed.
Lemma env_top_lp : forall sp tid a0 path inp data rnd J buf g len cap,
bv_unsigned sp <= 2 ^ 47 -> env_top (E_lp sp tid a0 path inp data rnd J buf g len cap).
Proof. intros. unfold env_top. rewrite ew_lp. cbn. exact H. Qed.
Ltac etop_sync HS HT :=
lazymatch type of HS with
| st_ok _ (havoc ?E ?k ?ws) _ _ => apply (env_top_havoc E k ws) in HT; [| lia]
| st_ok _ (post_env ?E ?k ?regs ?g) _ _ => apply (env_top_post E k regs g) in HT; [| lia]
| _ => idtac
end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition md_invX (fs : Fs) (md : Model) : Prop :=
(forall k, fd_lookup (m_fds md) k = fd_lookup STDFDS k) /\
fd_names_path (m_fds md) sink_path = false /\
m_fs md = fs /\ Fs.fs_sorted fs = true.
Lemma md_invX_inv : forall fs md, md_invX fs md -> md_inv fs md.
Proof.
intros fs md (H1 & H2 & H3 & H4). unfold md_inv, fdchan. rewrite !H1. cbn. repeat split; try reflexivity; try discriminate. exact H3.
Qed.
Lemma md_invX_ch1 : forall fs md, md_invX fs md -> fdchan (Z_to_bv 64 1) ch_stdout md.
Proof. intros fs md H. exact (md_inv_ch1 _ _ (md_invX_inv _ _ H)). Qed.
Lemma md_invX_fs : forall fs md, md_invX fs md -> m_fs md = fs.
Proof. intros fs md (_ & _ & H & _). exact H. Qed.
Lemma md_invX_sorted : forall fs md, md_invX fs md -> Fs.fs_sorted (m_fs md) = true.
Proof. intros fs md (_ & _ & -> & H). exact H. Qed.
Lemma md_invX_names : forall fs md, md_invX fs md -> fd_names_path (m_fds md) sink_path = false.
Proof. intros fs md (_ & H & _). exact H. Qed.
Lemma md_invX_vm : forall fs md vm, md_invX fs md -> md_invX fs (with_vmmaps vm md).
Proof. intros fs md vm (H1 & H2 & H3 & H4). unfold md_invX. autorewrite with model. repeat split; assumption. Qed.
Lemma md_invX_ex : forall fs md md', md_invX fs md -> (exists vm, md' = with_vmmaps vm md) -> md_invX fs md'.
Proof. intros fs md md' H [vm ->]. apply md_invX_vm. exact H. Qed.
Lemma md_invX_of_post : forall inp md, valid_fs (in_fs inp) -> md_post inp md -> md_invX (in_fs inp) md.
Proof.
intros inp md Hv (_ & _ & Hfs & Hfds). unfold md_invX. rewrite Hfds. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hfs|]. destruct Hv as (Hs & _). exact Hs.
Qed.
Lemma alloc_fd_aux_ext : forall f1 f2, (forall k, fd_lookup f1 k = fd_lookup f2 k) -> forall fuel c, alloc_fd_aux f1 c fuel = alloc_fd_aux f2 c fuel.
Proof. intros f1 f2 H. induction fuel as [|fuel IH]; intros c; cbn; [reflexivity|]. rewrite H. destruct (fd_lookup f2 c); [apply IH | reflexivity]. Qed.
Lemma md_invX_free : forall fs md, md_invX fs md -> fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Proof.
intros fs md (H1 & _). unfold alloc_fd. rewrite (alloc_fd_aux_ext _ _ H1), H1. vm_compute. reflexivity.
Qed.
Lemma md_invX_lib : forall fs md md' fs' (mem' : word -> option byte),
md_invX fs md ->
(exists vm' fds' pins', md' = os_upd vm' fds' fs' pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) ->
sink_none src0_msyms mem' md' -> Fs.fs_sorted fs' = true ->
md_invX fs' md'.
Proof.
intros fs md md' fs' mem' (H1 & H2 & H3 & H4) (vm' & fds' & pins' & -> & Hl) (_ & _ & Hn) Hs'.
unfold md_invX. rewrite os_upd_fds, os_upd_fs in *. split; [intros k; rewrite Hl; apply H1|]. split; [exact Hn|]. split; [reflexivity | exact Hs'].
Qed.
Lemma payload_len_length : forall data, 6 + config_len data <= dlen data -> payload_len data = Z.of_nat (length (payload data)).
Proof. intros data H. symmetry. apply payload_length. unfold HDR_MIN. exact H. Qed.
Lemma payload_nil : forall data, 6 + config_len data <= dlen data -> payload_len data = 0 -> payload data = [].
Proof.
intros data H H0. pose proof (payload_len_length data H) as L. rewrite H0 in L.
destruct (payload data); [reflexivity | cbn in L; lia].
Qed.
Lemma driver_tail_run_eq' : forall data buf cap s,
HDR_MIN <= dlen data -> HDR_MIN + config_len data <= dlen data -> payload_len data = 0 ->
driver_tail data (RdLoaded buf cap) s = ret (DL_run buf cap None) s.
Proof.
intros data buf cap s H1 H2 H3. unfold driver_tail.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2), (proj2 (Z.eqb_eq _ _) H3). reflexivity.
Qed.
Lemma res_of_tail_none : forall (P : dleaf * astate -> Prop) data b0 cap0 A',
leaves P (driver_tail data (RdLoaded b0 cap0) A') ->
6 + config_len data <= dlen data -> payload_len data = 0 -> P (DL_run b0 cap0 None, A').
Proof.
intros P data b0 cap0 A' HL Hok Hpl. pose proof (config_len_bound data). rewrite (driver_tail_run_eq' data b0 cap0 A') in HL by (unfold HDR_MIN; lia). exact HL.
Qed.
Lemma res_of_tail_some : forall (P : dleaf * astate -> Prop) data b0 cap0 A',
leaves P (driver_tail data (RdLoaded b0 cap0) A') ->
6 + config_len data <= dlen data -> payload_len data <> 0 ->
forall tr r, cpath (malloc (payload_len data) A') tr r -> P (payload_leaf b0 cap0 r).
Proof.
intros P data b0 cap0 A' HL Hok Hpl tr [p s'] Hp. pose proof (config_len_bound data).
rewrite (driver_tail_loaded_eq data b0 cap0 A') in HL;
[| apply Z.ltb_ge; unfold HDR_MIN; lia | apply Z.ltb_ge; unfold HDR_MIN; lia | apply Z.eqb_neq; exact Hpl].
unfold bind in HL. apply leaves_ibind_inv in HL.
pose proof (leaves_cpath _ _ _ _ HL Hp) as HX. cbn beta in HX. destruct p; cbn in HX; exact HX.
Qed.
Lemma src0_env_rom : forall mem : word -> option byte,
(forall a, env_addr a -> mbyte src0segs mem a = seg_rom src0segs (Z_to_bv 64 a)) ->
closed_stdio_env src0_msyms mem /\ word_mem src0segs mem sk_ofl_head 0.
Proof.
intros mem Hrom.
assert (R : forall a, env_addr a -> forall v, seg_rom src0segs (Z_to_bv 64 a) = v -> mbyte src0segs mem a = v)
by (intros a Ha v <-; apply Hrom; exact Ha).
split; [split|].
all: try (intros j Hj; cbn in Hj;
do 14 (destruct j as [|j]; [first [lia | split; [intros k Hk; destruct k as [|k]; [apply R; [unfold env_addr; cbn; lia | vm_compute; reflexivity] | cbn in Hk; lia] | cbn; lia]] |]); lia).
all: try (intros k Hk; do 8 (destruct k as [|k]; [apply R; [unfold env_addr; cbn; lia | vm_compute; reflexivity] |]); cbn in Hk; lia).
Qed.
Section d.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr) (MDc : Model).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis Hok : 6 + config_len data <= dlen data.
Hypothesis HLc : dlen data < cap0.
Theorem src0_P_to_QX : forall E ms T,
run_env E data (ptr_addr L' b0) ->
st_ok src0segs E (if config_len data =? 0 then ssP0 else ssP1) ms ->
aa_MR API L' A' (ms_mem ms) MDc ->
blk_data src0_msyms (ms_mem ms) (ptr_addr L' b0) data ->
(forall ms', st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms' ->
aa_MR API L' A' (ms_mem ms') MDc ->
blk_data src0_msyms (ms_mem ms') (ptr_addr L' b0) data ->
realizes src0segs (mkCfg ms' MDc) T) ->
realizes src0segs (mkCfg ms MDc) T.
Proof.
intros E ms T HE HS HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof HE as HE0. destruct HE as (HEd & HE13 & HE26 & HE46 & HAN). unfold dlen in *.
destruct (list_len2 data ltac:(pose proof (config_len_bound data); lia)) as (d0 & d1 & rest & Ed).
let v := eval cbv [sv_cl00 add0 sv_cl sv_b1s] in sv_cl00 in
assert (Hcl00 : U E v = config_len data) by (eapply U_cl00; eauto).
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hnz].
- drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB0 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_eq_U, Hcl00, U_SLit, Hz. reflexivity. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ0 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR HD).
- drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB1 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_eq_U, Hcl00, U_SLit. change (zcanon 0) with 0. apply Z.eqb_neq. exact Hnz. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ1 msx) in HS end.
drv_bd AX src0_keep E HS HF HMR HD Hin.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR HD).
Qed.
End d.
End b.
