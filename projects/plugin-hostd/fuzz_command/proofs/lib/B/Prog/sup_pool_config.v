(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00 YI0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG05 YG0q YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdChk CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtAPI RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c xmalloc_c record_c arg_s_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_pool_config_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaArtOwn PaFx CmdRecFacts RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns sup_pool_config_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the walk was built under PaDenot.v's former global division flag (div / mod as atoms); a later change made it Local *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the realignment `andi sp,sp,-32` (0x8bf08) on the entry sp less 96 is CmdSnText's snt_sp1_facts /
   snt_denot_and_m32; two denotation steps of the walk ---------- *)
Lemma spcb_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma spcb_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
(* cgif's region_kept over aview for a region whose window bytes stay present (answer_code.v's region_kept_hi2) *)
Lemma spcb_region_kept_hi {fx : YK11.FPState} : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

(* ---------- region trimming (lib/A/Prog/arg_i_s1.v's chunk_in, trim_region, trim_stack, subregion_tac,
   submem_to) ---------- *)
Definition spcb_chunk_in (lo hi : Z) (c : YP09.chunk) : bool :=
Z.leb lo (YP09.c_off c) && Z.leb (YP09.c_off c + YP09.c_len c) hi.
Definition spcb_trim_region (r : YP09.region) (lo hi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) lo hi (Z.max (YP09.r_wlo r) lo) (Z.min (YP09.r_whi r) hi)
(filter (spcb_chunk_in lo hi) (YP09.r_chunks r)).
Ltac spcb_subregion_tac :=
unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|];
let c := fresh "c" in let Hc := fresh "Hc" in intros c Hc; cbn in Hc |- *;
first [exact Hc | solve [destruct Hc] | tauto].
Ltac spcb_submem_to := repeat (first [apply submem_keep; [spcb_subregion_tac|] | apply submem_drop]); apply submem_nil.
Ltac spcb_norm HS := lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* a register's symbolic value, not normalised (answer_code.v's preg) *)
Ltac spcb_preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* an address outside every write window of a symbolic memory (answer_code.v's nwin_tac) *)
Ltac spcb_nwin rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.
Ltac spcb_mdclr := repeat match goal with
| |- context [with_vm_backing ?l ?m ?d] => let mdv := fresh "mdv" in set (mdv := with_vm_backing l m d) in *; clearbody mdv
end.

(* ---------- the entry state (arg_i's ai_entry, sup_after_reply's B twin sar_entry): the stack below the entry sp
   (the 96-byte frame and the realignment's 16), the shadow GOT word and cell, the use-after-return GOT word and
   flag ---------- *)
Definition spcb_regions0 : smem :=
[ stack_region 112; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition spcb_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (33%nat, mkAF 0x10000 0x606000 2) ].
Definition ss_spcb0 : sstate := mkSS AF_sup_pool_config sr_atoms spcb_regions0 None (mkFacts spcb_atoms0 [] []).
(* the atoms above the 32 registers: 32 the shadow base, 33 the use-after-return flag's cell *)
Definition spcb_extra0 (uar : Z) : list word := map (Z_to_bv 64) [SB; uar].
(* the bytes below alloc_ceiling the walk itself writes: its side-stack frame and the frame's eight shadow bytes *)
Definition spcb_zf (F a : Z) : Prop := F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8.

(* ---------- the snprintf call's side facts ---------- *)
Ltac spcb_fz := repeat (first [apply Forall_nil | apply Forall_cons]); unfold zdisjoint; cbn [fst snd]; lia.
(* the contract's read-only ranges lie in the image hull (RtPFCmd.cmd_snp_cr_img) *)
Lemma spcb_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) RtPFCmd.cmd_snp_cr_img r Hr) as H.
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
Lemma spcb_cr_bnd : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RtPFCmd.CMD_SNP_CR.
Proof. apply Forall_forall. intros r Hr. destruct (spcb_cr_img r Hr). lia. Qed.
Lemma spcb_cr_disj : forall K sp d w, 0x606000 <= sp - K -> 0 <= K -> 0 <= w -> (d + w <= 0x10000 \/ 0x606000 <= d) ->
Forall (fun r => Forall (zdisjoint r) (snp_out K sp d w)) RtPFCmd.CMD_SNP_CR.
Proof.
intros K sp d w H1 H2 H3 H4. apply Forall_forall. intros r Hr. destruct (spcb_cr_img r Hr) as (A1 & A2 & A3).
unfold snp_out. spcb_fz.
Qed.
(* a byte of a 1-byte chunk *)
Lemma spcb_aview_val1 : forall (segs : list Segment) (H : word -> bool) mem a v,
val_mem segs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview segs H mem a = Some v.
Proof.
intros segs H mem a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as H0.
change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. rewrite H0. cbn [option_map]. f_equal.
rewrite le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
(* b = frame + 32 with its two shadow bytes 00: addressable for up to 16 bytes, and its shadow hull is the frame's *)
Lemma spcb_b_shadow : forall (rd : reader) F w, F mod 64 = 0 -> 0 <= F -> 1 <= w <= 16 ->
rd (SB + F / 8 + 4) = Some 0 -> rd (SB + F / 8 + 5) = Some 0 ->
(forall s, SB + F / 8 <= s < SB + F / 8 + 8 -> rd s <> None) ->
range_addressable rd SHADOW_OFF (F + 32) w /\ shadow_hull_vis rd (F + 32) w.
Proof.
intros rd F w HF HF0 Hw H4 H5 H8.
pose proof (Z.div_mod F 64 ltac:(lia)) as D64. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
assert (E8 : F / 8 = 8 * (F / 64)) by lia.
split.
- intros y Hy. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
  pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
  assert (Hq : y / 8 = F / 8 + 4 \/ y / 8 = F / 8 + 5) by lia.
  destruct Hq as [-> | ->]; [replace (SB + (F / 8 + 4)) with (SB + F / 8 + 4) by lia; exact H4
    | replace (SB + (F / 8 + 5)) with (SB + F / 8 + 5) by lia; exact H5].
- intros s Hs. apply H8. unfold shadow_addr in Hs. rewrite <- SB_SHADOW_OFF in Hs.
  pose proof (Z.div_mod (F + 32) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (F + 32) 8 ltac:(lia)).
  pose proof (Z.div_mod (F + 32 + w - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (F + 32 + w - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (SB + (F + 32) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (F + 32) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SB + (F + 32 + w - 1) / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + (F + 32 + w - 1) / 8) 8 ltac:(lia)).
  unfold SB in *. lia.
Qed.
(* the text snprintf left at d, as the string it is *)
Lemma spcb_str_of_pf : forall (rd : reader) d (T : list Z),
(forall i, 0 <= i < Z.of_nat (length T) + 1 -> rd (d + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
(forall a z, rd a = Some z -> 0 <= z < 256) -> ~ In (Z_to_bv 8 0) (PF.pf_bytes T) -> astr_atR rd d (PF.pf_bytes T).
Proof.
intros rd d T H Hr Hn. split; [|exact Hn]. intros i Hi.
unfold PF.pf_bytes in *. rewrite length_app, length_map in Hi. cbn [length] in Hi.
replace (map (Z_to_bv 8) T ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (T ++ [0])) by (rewrite map_app; reflexivity).
pose proof (H (Z.of_nat i) ltac:(lia)) as Hi'. rewrite Nat2Z.id in Hi'. rewrite Hi'.
rewrite (map_nth (Z_to_bv 8) (T ++ [0]) 0 i). f_equal.
pose proof (Hr _ _ Hi') as Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact Hz.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---------- reading the symbolic state, and moving it to another FP state ---------- *)
(* B/YF0x.v's st_ok_chunk_val over any segments, a chunk given by membership *)
Lemma spcb_chunk_val : forall (fx0 : YK11.FPState) (segs : list Segment) (H : word -> bool) E ss ms r off (n : N) e,
@st_ok segs fx0 E ss (restrict H ms) -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) -> forall v,
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem segs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros fx0 segs H E ss ms r off n e HS Hr Hc v He Hv Hn.
pose proof (st_ok_mem_ok segs E ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
apply (val_of_chunk_ok segs E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.
Lemma spcb_region_val : forall (segs : list Segment) E m r off (n : N) e v,
region_ok segs E m r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem segs m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros segs E m r off n e v (_ & _ & _ & Hcs) Hc He Hv Hn.
apply (val_of_chunk_ok segs E _ _ off n e v); [|exact He | exact Hv | exact Hn].
exact (proj1 (Forall_forall _ _) Hcs _ Hc).
Qed.
Fixpoint spcb_find_chunk (off : Z) (cs : list YP09.chunk) : option YP09.chunk :=
match cs with [] => None | c :: t => if Z.eqb (YP09.c_off c) off then Some c else spcb_find_chunk off t end.
Lemma spcb_find_chunk_in : forall off cs c, spcb_find_chunk off cs = Some c -> In c cs.
Proof.
intros off cs c. induction cs as [|c0 t IH]; cbn [spcb_find_chunk]; [discriminate|].
destruct (Z.eqb _ _); [intros H; injection H as ->; left; reflexivity | intros H; right; exact (IH H)].
Qed.
(* the value of the chunk at offset off of the i-th region of a concrete symbolic state *)
Ltac spcb_chunk HS i off H :=
lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
  let r := eval vm_compute in (nth i (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
  let c := eval vm_compute in (spcb_find_chunk off (YP09.r_chunks r)) in
  lazymatch c with Some (YP09.mkChunk ?o (CVal ?n ?e)) =>
    let Hr := fresh "Hr" in let Hc := fresh "Hc" in
    assert (Hr : nth_error (ss_mem ss) i = Some r) by (vm_compute; reflexivity);
    assert (Hc : spcb_find_chunk off (YP09.r_chunks r) = Some (YP09.mkChunk o (CVal n e))) by (vm_compute; reflexivity);
    pose proof (spcb_chunk_val _ segs Hh E ss ms r o n e HS (nth_error_In _ _ Hr) (spcb_find_chunk_in _ _ _ Hc)) as H;
    clear Hr Hc; cbn [YP09.r_base base_val] in H
  end end.


Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---------- the entry state's seed (sar_entry) ---------- *)
Section c2.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Lemma spcb_entry : forall STK W ly S regs mem md ch,
112 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (spcb_extra0 (as_uar_cell B)))) ss_spcb0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_pool_config)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HSTK HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (spcb_extra0 (as_uar_cell B)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_spcb0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold spcb_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 33%nat (as_uar_cell B) E33) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold spcb_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 C3 HSTK Hstk0 Hob0 Hob1 Hob12 Huar Hsep. clear.
  unfold ASAN_CEIL. intros.
  rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
  repeat split; first [ assumption | (apply or_comm; assumption)
  | (repeat match goal with H : _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok spcb_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33.
  rewrite !unsigned_lit_small by (unfold SB in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
Qed.
End c2.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_pool_config_c.v, a Theorem Labs lane 707acd856cb), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses (a Theorem Labs lane's naming rule: a fact a Theorem Labs lane states only at PI := PB_cmd is taken at this walk's
   abstract PAImg under the lemma's name; RECB-NAMED-HYPS.md for the others): HB, the per-binary
   allocator record (lib/B/YF0m.v CmdBSyms); MTL and MTLF, the meter's laws and their side-stack form (YC5d.v);
   cmd_sig_prog_PB, the program functions' call targets; cmd_palib, the trampolines' pcs and the shadow cells;
   cmd_palibf, the side-stack entries' pcs and the use-after-return cells; cmd_frame_flag_law, a live side-stack
   frame's flag byte (all four of a Theorem Labs lane's CmdRecRest.v lemmas at PB_cmd, a working branch 707acd856cb);
   cmd_img_facts_tfib, the image facts (a Theorem Labs lane's CmdRecImg.v). The model laws and the side-stack progress are a Theorem Labs lane's
   CmdRecRest.cmd_model_laws / cmd_stack_malloc_progress, which hold at any image, and the program statics' apartness
   is RecBLemmas.recb_prog_unowned_m. *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib B0.
Hypothesis cmd_palibf : forall B0, CmdBSyms B0 -> PALibF B0.
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let TL : PALib B := cmd_palib B HB.
Let TLF : PALibF B := cmd_palibf B HB.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let ML : model_laws (as_universe B) := CmdRecRest.cmd_model_laws B HB.
(* a Theorem Labs lane's per-binary facts over IMG, by exact (CmdRecRo.v, CmdRecRest.v, CmdRecImg.v, CmdRecCells.v) *)
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_atail_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' p n e,
  AR SEGS B ly S W mem md -> AR SEGS B ly' S' W' mem' md' ->
  ((In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= e < p + n) \/
   (in_roP SEGS RLO RHI e /\ ~ Exists (in_zr e) (as_owned_static B))) ->
  atail_vis SEGS W mem e -> atail_vis SEGS W' mem' e :=
  CmdRecRest.cmd_atail_kept (SK := SK) SEGS B LAWS HB IMG.
Let cmd_rodata_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' STK sp0 FP own k,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, inFP FP a -> Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n) ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') :=
  CmdRecRest.cmd_rodata_kept (SK := SK) SEGS B LAWS HB IMG.
Let cmd_rec_cells : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  rdW W mem 0xae455 = Some 1 /\ aguard_ok SEGS W mem 0xa6bf8 0x604158 /\ exists ev, rd32 (rdW W mem) (as_errno B) ev :=
  CmdRecCells.cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.

(* ---------- the recorder's blocks, the footprint and what a journal keeps: sup_reset's B walk helpers
   (a working branch c79a9f2daf7 lib/B/Prog/sup_reset.v:339-636, srb_ renamed spr_) ---------- *)
(* ---------- the allocator's blocks ---------- *)

Lemma spr_O_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HOQ pn) Hpn)). Qed.

Lemma spr_blk_bounds : forall ly S (W : world SEGS) mem md b m, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> 4096 <= b /\ b + req_size m <= alloc_ceiling /\ 0 <= m /\ m <= req_size m /\ 1 <= req_size m.
Proof.
intros ly S W mem md b m HAR Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [Hq1 Hq2]. lia.
Qed.

Lemma spr_blk_noimg : forall ly S (W : world SEGS) mem md b m a, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> b <= a < b + req_size m -> ~ in_img SEGS a.
Proof.
intros ly S W mem md b m a HAR Hin Ha.
exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

Lemma spr_blk_apart : forall ly S (W : world SEGS) mem md b m p n, AR SEGS B ly S W mem md ->
In (b, m) (ablocks B ly S) -> In (p, n) (ablocks B ly S) -> (b, m) <> (p, n) ->
b + req_size m <= p \/ p + req_size n <= b.
Proof.
intros ly S W mem md b m p n HAR H1 H2 Hne.
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR H1 H2 Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma spr_same_start : forall ly S (W : world SEGS) mem md pn an, AR SEGS B ly S W mem md ->
In pn (ablocks B ly S) -> In an (ablocks B ly S) -> fst pn = fst an -> pn = an.
Proof.
intros ly S W mem md [b m] [b' m'] HAR H1 H2 Hf. cbn [fst] in Hf. subst b'.
destruct (spr_pair_dec (b, m) (b, m')) as [E | Hne]; [exact E|]. exfalso.
destruct (spr_blk_bounds ly S W mem md b m HAR H1) as (_ & _ & _ & _ & R1).
destruct (spr_blk_bounds ly S W mem md b m' HAR H2) as (_ & _ & _ & _ & R2).
destruct (spr_blk_apart ly S W mem md b m b m' HAR H1 H2 Hne); lia.
Qed.

(* a live block is listed once *)
Lemma spr_dup_false : forall ly S (W : world SEGS) mem md L1 L2 pn, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) (L1 ++ L2) -> In pn L1 -> In pn L2 -> False.
Proof.
intros ly S W mem md L1 L2 pn HAR HP H1 H2.
pose proof H1 as H1'.
apply in_split in H1 as (a1 & b1 & ->). apply in_split in H2 as (a2 & b2 & ->).
assert (HP' : Permutation (ablocks B ly S) (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2))).
{ eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app].
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  replace (a1 ++ b1 ++ a2 ++ pn :: b2) with ((a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite <- !app_assoc. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP') as D.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact H1').
destruct pn as [b m].
destruct (spr_blk_bounds ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & Hr1).
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

(* ---------- the walk's footprint and what a journal keeps ---------- *)

Lemma spr_inFP_cases : forall O a, inFP (spr_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists b n, In (b, n) O /\ b <= a < b + req_size n.
Proof.
intros O a (r & Hr & Ha). unfold spr_FP in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply spr_grec_in. exact Ha.
- left. apply spr_spill_in. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hin). cbn [fst snd] in Ha.
  exists b, n. split; [exact Hin | exact Ha].
Qed.

Lemma spr_static_low : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> 0x10000 <= a < 0x606000.
Proof. intros a Ha. exact (pa_img_range a (cmd_prog_img a Ha)). Qed.

Lemma spr_FP_low : forall ly S (W : world SEGS) mem md O a, AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) -> inFP (spr_FP O) a -> 0 <= a < alloc_ceiling.
Proof.
intros ly S W mem md O a HAR HO Ha. pose proof asan_consts as (C1 & _).
destruct (spr_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)].
- pose proof (spr_static_low a HP). lia.
- destruct (spr_blk_bounds ly S W mem md b n HAR (HO _ Hin)) as (H4 & Hc & _). lia.
Qed.

(* arodata_okP along the walk's journal (cmd_rodata_kept: the footprint is statics and the recorder's blocks) *)
Lemma spr_aro : forall ly S (W : world SEGS) mem md O lyc Sc Wc memc mdc own k sp STK,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
ajournal SEGS B STK sp (spr_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros ly S W mem md O lyc Sc Wc memc mdc own k sp STK HAR HO HJ HR.
apply (cmd_rodata_kept ly S W mem md lyc Sc Wc memc mdc STK sp (spr_FP O) own k HAR HJ); [|exact HR].
intros a Ha. destruct (spr_inFP_cases O a Ha) as [HP | (b & n & Hin & Hb)]; [left; exact HP|].
right. exists b, n. split; [apply in_or_app; left; exact (HO _ Hin) | exact Hb].
Qed.

Lemma spr_keep_img : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
apply F3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [apply sink_closed_pos; exact HF | exact Hn]].
Qed.


Lemma spr_keep_prog : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
Forall (fun r => 0 < fst r) FP1 -> ~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC ->
rdW W2 mem2 a = rdW Wc memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ HF Hn HP.
destruct ((recb_prog_unowned_m B HB cmd_prog_img) a HP) as (H1 & H2 & H3). exact (spr_keep_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ HF Hn H1 H2 H3).
Qed.

Lemma spr_keep_blk : forall STK1 sp1 FP1 lyc Sc (Wc : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 b m i,
ajournal SEGS B STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 ->
In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> 0 <= i < req_size m -> ~ inFP FP1 (b + i) ->
rdW W2 mem2 (b + i) = rdW Wc memc (b + i).
Proof.
intros STK1 sp1 FP1 lyc Sc Wc memc mdc own ly2 S2 W2 mem2 md2 k1 b m i HJ H1 H2 Hi Hn.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). exact (F2 b m i H1 H2 Hi Hn).
Qed.

(* the frame chain of s0 = the entry sp at a call of the walk (PASS4-REFIT.md section B, class B): afn_pre's chain
   at the entry sp with the prologue's ra and caller's s0 words on top (achain_push), moved to the call's layout *)
Lemma spcb_chain : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k v ch ra sp',
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch ->
rdword (rdW Wc memc) (sp0 - 8) = Some ra -> rdword (rdW Wc memc) (sp0 - 16) = Some v -> 4096 <= ra ->
sp' + 16 <= sp0 ->
exists ch1, achain lyc (rdW Wc memc) sp' sp0 ch1.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k v ch ra sp' HJ HF Hc H8 H16 Hra Hsp.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (Z_lt_le_dec sp0 (ly_top ly - 16)) as [Hlt | Hge].
- exists ((sp0, ra, v) :: ch). apply (achain_ly_top ly lyc); [exact Etop|].
  apply (achain_push ly (rdW W mem) (rdW Wc memc) sp0 v ra ch sp' Hc); try lia.
  + intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
  + exact H8.
  + exact H16.
  + pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)).
    pose proof (Z.div_mod sp0 8 ltac:(lia)). lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

Lemma spr_achain_kept : forall STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k v ch,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
(forall a, inFP FP a -> a < alloc_ceiling) ->
achain ly (rdW W mem) sp0 v ch -> achain ly' (rdW W' mem') sp0 v ch.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k v ch HJ HF Hc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & Hs0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top ly ly'); [exact Etop|].
apply (achain_kept ly (rdW W mem) (rdW W' mem') sp0 v ch sp0 Hc); [lia | lia |].
intros a Ha. apply F1; [lia | lia | intros Hf; specialize (HF a Hf); lia].
Qed.

(* the bytes the walk's callees may write: g_rec / record.spill (program statics), and the recorder's own blocks *)
Lemma spr_awr_static : forall STK sp O bl0 blc fr0 ly own a, Exists (in_zr a) TFIB_PROG_STATIC -> inFP (spr_FP O) a ->
awr_byte SEGS B STK sp (spr_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a HP HF.
right; right; right; right; left. split; [exact HF|]. split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)].
Qed.

Lemma spr_awr_grec : forall STK sp O bl0 blc fr0 ly own a, A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp (spr_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply spr_awr_static; [exact (spr_grec_in a Ha)|].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

Lemma spr_awr_spill : forall STK sp O bl0 blc fr0 ly own a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE ->
awr_byte SEGS B STK sp (spr_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own a Ha. apply spr_awr_static; [exact (spr_spill_in a Ha)|].
exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* a byte of the slot record() returned *)
Lemma spr_awr_slot : forall STK sp O bl0 blc fr0 ly own R a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + CALL_SIZE -> awr_byte SEGS B STK sp (spr_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own R a HL Ha. destruct (spr_slot_bounds R HL) as [Hs | Hs].
- apply spr_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
- apply spr_awr_spill. rewrite Hs in Ha. unfold SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma spr_awr_blk : forall STK sp O bl0 blc fr0 ly own b n a, In (b, n) O -> In (b, n) blc ->
b <= a < b + req_size n -> awr_byte SEGS B STK sp (spr_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp O bl0 blc fr0 ly own b n a HO Hc Ha. right; left. split.
- unfold spr_FP. apply inFP_cons. right. apply inFP_cons. right.
  replace a with (b + (a - b)) by lia. apply (inFP_ablocks_fp O b n (a - b)); [exact HO | lia].
- exists b, n. split; [exact Hc | exact Ha].
Qed.

(* ---------- the string argument ---------- *)

(* the bytes of a string argument decide astr_argA's reader part: its other parts name no reader *)
Lemma spr_argA_kept : forall ly1 S1 (rd rd' : reader) ro O1 p v, astr_argA B ly1 S1 rd ro O1 p (Some v) ->
(forall i, 0 <= i < Z.of_nat (length v) + 1 -> rd' (p + i) = rd (p + i)) -> astr_argA B ly1 S1 rd' ro O1 p (Some v).
Proof.
intros ly1 S1 rd rd' ro O1 p v H K. cbn [astr_argA] in H |- *. destruct H as (H0 & Hs & Hl & Hr).
split; [exact H0|]. split; [|split; [exact Hl | exact Hr]].
apply (spr_str_keep rd); [exact Hs|]. intros x Hx. replace x with (p + (x - p)) by lia. apply K. lia.
Qed.

(* a string argument's bytes lie below alloc_ceiling: a block's, or the image's *)
Lemma spr_argA_low : forall ly1 S1 (W1 : world SEGS) mem1 md1 O1 p v, AR SEGS B ly1 S1 W1 mem1 md1 ->
astr_argA B ly1 S1 (rdW W1 mem1) (in_roP SEGS RLO RHI) O1 p (Some v) ->
forall i, 0 <= i < Z.of_nat (length v) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 O1 p v HAR H i Hi. cbn [astr_argA] in H. pose proof asan_consts as (C1 & _).
destruct H as (_ & _ & _ & [(Hblk & _) | (Hro & _)]).
- destruct Hblk as (b & m & Hin & Hb1 & Hb2).
  destruct (spr_blk_bounds ly1 S1 W1 mem1 md1 b m HAR Hin) as (Hb & Hc & _ & Hmr & _). lia.
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))). lia.
Qed.

(* the pointer itself (caller's s0 at the program calls) lies below alloc_ceiling *)
Lemma spr_pw_low : forall ly S (W : world SEGS) mem md O pw which, AR SEGS B ly S W mem md ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw which -> 0 <= pw < alloc_ceiling.
Proof.
intros ly S W mem md O pw which HAR H. pose proof asan_consts as (C1 & _). destruct which as [x|].
- pose proof (spr_argA_low ly S W mem md O pw x HAR H 0 ltac:(lia)). lia.
- cbn [astr_argA] in H. subst pw. lia.
Qed.

(* the string argument from the entry to a later state: its block (none of the recorder's) is live there with its
   bytes, or its read-only bytes are the image's at both states; its word tail is kept (cmd_atail_kept) *)
Lemma spr_arg_kept : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O pw x,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k -> rdW Wc memc a = rdW W mem a) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pw (Some x) ->
atail_vis SEGS W mem (pw + Z.of_nat (length x)) ->
astr_argA B lyc Sc (rdW Wc memc) (in_roP SEGS RLO RHI) [] pw (Some x) /\
atail_vis SEGS Wc memc (pw + Z.of_nat (length x)).
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O pw x HAR HARc HRO HROc Hblk Hbytes HA HT.
cbn [astr_argA] in HA |- *.
destruct HA as (Hp0 & HS & Hlen & [((b & k & Hbk & Hble & Hhi) & Hap) | (Hro & Hck)]).
- assert (HnO : ~ In (b, k) O).
  { intros Hin. rewrite Forall_forall in Hap. pose proof (Hap (b, k) Hin) as Hd. cbn [fst snd] in Hd.
    unfold iv_apart in Hd. lia. }
  assert (HK : forall a, b <= a < b + k -> rdW Wc memc a = rdW W mem a)
    by (intros a Ha; exact (Hbytes b k a Hbk HnO Ha)).
  split.
  + split; [exact Hp0|]. split.
    * apply (spr_str_keep (rdW W mem)); [exact HS|]. intros a Ha. apply HK. lia.
    * split; [exact Hlen|]. left. split; [|apply Forall_nil].
      exists b, k. split; [exact (Hblk (b, k) Hbk HnO) | split; [exact Hble | exact Hhi]].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc b k (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | left; split; [exact Hbk | split; [exact (Hblk (b, k) Hbk HnO) | lia]] | exact HT].
- split.
  + split; [exact Hp0|]. split.
    * apply (spr_str_keep (rdW W mem)); [exact HS|]. intros a Ha.
      destruct (Hro (a - pw) ltac:(lia)) as (Hr & Ho & He). replace a with (pw + (a - pw)) by lia.
      rewrite (HROc _ Hr Ho He), (HRO _ Hr Ho He). reflexivity.
    * split; [exact Hlen|]. right. split; [exact Hro | exact Hck].
  + apply (cmd_atail_kept ly S W mem md lyc Sc Wc memc mdc 0 0 (pw + Z.of_nat (length x)));
    [exact HAR | exact HARc | right | exact HT].
    destruct (Hro (Z.of_nat (length x)) ltac:(lia)) as (Hr & Ho & _). split; [exact Hr | exact Ho].
Qed.

(* rec_repA at a state whose reader agrees on g_rec, record.spill and the recorder's blocks *)
Lemma spr_rec_repA_ext : forall ly S rd ly' S' rd' R O,
  rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros ly S rd ly' S' rd' R O (Q & HR & HO) KB K. exists Q. split; [|exact HO].
  apply (spr_arep_at_ext (ablocks B ly S) _ rd _ _ _ _ _ HR).
  - intros pn Hpn. apply KB. apply HO. exact Hpn.
  - intros a [Ha|[Ha|(pn & Hpn & Ha)]]; apply K;
      [left; exact Ha | right; left; exact Ha | right; right; exists pn; split; [apply HO; exact Hpn | exact Ha]].
Qed.

(* a block answer frees: the recorder's block whose start is the old answer (answer_c.v:137) *)
Lemma spr_in_filter : forall (old : Z) (l : list (Z * Z)) pn,
In pn (filter (fun pn => fst pn =? old) l) -> In pn l /\ fst pn = old.
Proof.
intros old l pn. induction l as [|a l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) as [Hd | Hd] in H.
- destruct H as [<- | H].
  + split; [left; reflexivity|]. revert Hd. destruct (fst a =? old) eqn:E; intros Hd; [apply Z.eqb_eq; exact E | destruct Hd].
  + destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
- destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.


(* ---------- a live side-stack frame's bytes and shadow bytes are present ---------- *)
Lemma spcb_frame_pres : forall ly S (W : world SEGS) mem md cid pos a, AR SEGS B ly S W mem md -> In (cid, pos) (frames S) ->
(frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
 shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
apresent (w_H W) mem a.
Proof.
intros ly S W mem md cid pos a HAR Hin Ha.
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hp & Hs).
destruct Ha as [Ha | Ha]; [exact (proj1 (Hp a Ha))|].
replace a with (shadow_addr (frame_addr ly cid pos) + (a - shadow_addr (frame_addr ly cid pos))) by lia.
exact (proj1 (Hs (a - shadow_addr (frame_addr ly cid pos)) ltac:(lia))).
Qed.

(* ---------- the program's statics and the live blocks are apart from the walk's frame and its shadow ---------- *)
Lemma spcb_nzf : forall ly S (W : world SEGS) mem md fpos a, AR SEGS B ly S W mem md -> In (0, fpos) (frames S) ->
(Exists (in_zr a) TFIB_PROG_STATIC \/ exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) ->
a < alloc_ceiling /\ ~ spcb_zf (frame_addr ly 0 fpos) a.
Proof.
intros ly S W mem md fpos a HAR Hin Ha.
pose proof (frm_off_imgP B ly S W mem md 0 fpos HAR Hin) as Hoff.
destruct (frames_bounds SEGS B LAWS ly S W mem md 0 fpos HAR Hin) as (H4 & Hc & Happ).
change (fs_frame_bytes 0) with 64 in Hoff, Hc, Happ.
set (F := frame_addr ly 0 fpos) in *.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold spcb_zf, off_img, SB in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
destruct Ha as [HP | (b & m & Hbm & Hba)].
- pose proof (spr_static_low a HP) as Hs. split; [lia|]. lia.
- pose proof (sep_block_frame SEGS B LAWS ly S W mem md b m 0 fpos HAR Hbm Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hbm) as (_ & Hb4 & Hbc & Hbapp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. split; [lia|]. lia.
Qed.
Lemma spcb_fp_apart : forall ly S (W : world SEGS) mem md fpos a, AR SEGS B ly S W mem md -> In (0, fpos) (frames S) ->
(A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
 exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) ->
a < alloc_ceiling /\ ~ spcb_zf (frame_addr ly 0 fpos) a.
Proof.
intros ly S W mem md fpos a HAR Hin Ha. apply (spcb_nzf ly S W mem md fpos a HAR Hin).
destruct Ha as [Ha | [Ha | Ha]]; [left; exact (spr_grec_in a Ha) | left; exact (spr_spill_in a Ha) | right; exact Ha].
Qed.
(* a string argument's bytes (astr_argA: a live block's, or the read-only image's) are apart from the frame *)
Lemma spcb_argA_nzf : forall ly S (W : world SEGS) mem md fpos O p v i, AR SEGS B ly S W mem md -> In (0, fpos) (frames S) ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some v) -> 0 <= i < Z.of_nat (length v) + 1 ->
0 <= p + i < alloc_ceiling /\ ~ spcb_zf (frame_addr ly 0 fpos) (p + i).
Proof.
intros ly S W mem md fpos O p v i HAR Hin H Hi. cbn [astr_argA] in H.
destruct H as (_ & _ & _ & [((b & m & Hbm & Hb1 & Hb2) & _) | (Hro & _)]).
- destruct (spr_blk_bounds ly S W mem md b m HAR Hbm) as (Hb & Hc & Hm0 & Hmr & _).
  destruct (spcb_nzf ly S W mem md fpos (p + i) HAR Hin) as [Hlo Hz]; [right; exists b, m; split; [exact Hbm | lia]|].
  split; [lia | exact Hz].
- destruct (Hro i Hi) as (Hr & _). pose proof (pa_img_range _ (proj1 (cmd_ro_prog_apart _ Hr))) as Himg.
  pose proof (frm_off_imgP B ly S W mem md 0 fpos HAR Hin) as Hoff.
  destruct (frames_bounds SEGS B LAWS ly S W mem md 0 fpos HAR Hin) as (H4 & Hc & Happ).
  change (fs_frame_bytes 0) with 64 in Hoff, Hc.
  pose proof asan_consts as (C1 & _).
  pose proof (Z.div_mod (frame_addr ly 0 fpos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr ly 0 fpos) 8 ltac:(lia)).
  unfold spcb_zf, off_img, SB in *. split; [lia|]. lia.
Qed.



(* ---------- the call targets: record (0x8bfd0), arg_s (0x8bfdc, 0x8c008), rec_shape_of (0x8c020), answer
   (0x8c030) ---------- *)
Lemma spcb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma spcb_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof. rewrite (cmd_sig_prog_PB CS_rec_shape_of ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.
Lemma spcb_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof. rewrite (cmd_sig_prog_PB CS_answer ltac:(vm_compute; repeat first [left; reflexivity | right])). reflexivity. Qed.

(* after a symbolic run the model term grows: name it *)
Ltac spcb_md :=
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ =>
  let mdv := fresh "mdv" in set (mdv := m) in *; clearbody mdv end.

(* ---------- the walk ---------- *)
Theorem tsup_pool_config_holds : tsup_pool_config_spec B MT.
Proof.
unfold tsup_pool_config_spec.
intros ly S W regs mem md ch pn max name R O HPRE HFRM HROD HRO H10 Hpn H11 Hmax HNAME HREP HFR7 HEV HLIVE HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_POOL_CONFIG_STK = 16704) by (vm_compute; reflexivity).
assert (HSBv : SB = 0x7fff8000) by reflexivity.
assert (HSK : CMD_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (EFP : (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O = spr_FP O)
  by reflexivity.
rewrite EFP. set (FP := spr_FP O).
pose proof (spcb_entry B LAWS TL TLF SUP_POOL_CONFIG_STK W ly S regs mem md ch ltac:(rewrite FS; lia) HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_POOL_CONFIG_STK FP ly S W regs mem md ch HPRE) as HJ.
remember (Eimg (Ereg regs (spcb_extra0 (as_uar_cell B)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_sup_pool_config)) with (Z_to_bv 64 (BASE + AF_sup_pool_config)).
(* run 1: the prologue to 0x8bf10 (after `andi sp,sp,-32; mv s1,sp`) *)
paj_run_to_shc RUNTOP HS HJ (AF_sup_pool_config + 0x40).
{ unfold ss_spcb0, spcb_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
  repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
spcb_preg HS (2%bv : bv 5) R2. spcb_preg HS (9%bv : bv 5) R9.
(* sp1 = (sp - 96) & -32, the realigned stack pointer (atom 34): s1 and sp from here on; the stack region is cut to
   the saved registers (sp - 88 .. sp) and the word `sd s8,0(s1)` stores at sp1 becomes a region of its own *)
set (sp1 := 32 * ((spZ regs + -96) / 32)).
destruct (snt_sp1_facts (spZ regs + -96) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by lia. clear Hsp1r.
assert (DA : sv_denot E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) = Z_to_bv 64 sp1)
  by (apply snt_denot_and_m32; [exact Esp | lia | lia | lia]).
rewrite DA in R2. rewrite spcb_add0, DA in R9.
pose proof (st_ok_pi_havoc 34 E _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E 34 [Z_to_bv 64 sp1]) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall n, (n < 34)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
assert (E34 : ew E1 34 = Z_to_bv 64 sp1) by (rewrite HE1; exact (ew_havoc_new E 34 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAE1 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E1) by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE1.
assert (U34 : bv_unsigned (ew E1 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (V2 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite OLD1 by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
    ltac:(rewrite spcb_off0, E34; cbn [ms_regs restrict mkst]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
    ltac:(rewrite spcb_off0, E34; cbn [ms_regs restrict mkst]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS. clear R2 R9.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 34%nat (mkAF (2 ^ 46 - 112) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U34; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs' := eval vm_compute in (match ss_mem ssx with r0 :: t => spcb_trim_region r0 (-88) 0 :: t | [] => [] end) in
  pose proof (st_ok_pi_submem Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; spcb_submem_to) ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 12 ltac:(lia)) as Hob12.
pose proof (palf_uar_img B TLF) as Huar.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 34%nat) 0 8 0 8 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite U34; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); apply HJpres; rewrite FS; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U34, ?V2;
      repeat match goal with |- context [bv_unsigned (ew Ev ?k)] =>
        lazymatch k with 34%nat => fail | 2%nat => fail | 33%nat => fail | _ =>
        rewrite (img_env_atomP Ev k HEI1 ltac:(unfold A_TEXT, A_LIM; lia)), unsigned_lit_small by (pose proof (pa_val_range k); lia) end end;
      repeat match goal with |- context [bv_unsigned (ew Ev 33%nat)] => rewrite (OLD1 33%nat ltac:(lia)), E33, unsigned_lit_small by lia end;
      change (VAL 241) with (VAL (A_OBJ 0)); change (VAL 242) with (VAL (A_OBJ 1)); change (VAL 253) with (VAL (A_OBJ 12));
      repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
(* run 2: 0x8bf10 .. 0x8bf38: s3 := max, the shadow base and the use-after-return flag (1) through their GOT words,
   s4 := name, the flag's branch (not taken), a0 := 64 and the call of __asan_stack_malloc_0 *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite U34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
  repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
(* the call of __asan_stack_malloc_0 (0x8bf38) for the 64-byte class-0 frame *)
pmkst HS.
pose proof (palf_sm B TLF 0 ltac:(cbn [In]; left; reflexivity)) as SM0. cbn [cs_stack_malloc Z.eqb] in SM0. rewrite SM0.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite E34 in R2. rewrite OLD1, (EE 3%nat 3%bv eq_refl) in R3 by lia. rewrite OLD1, (EE 4%nat 4%bv eq_refl) in R4 by lia.
assert (Qsp2 : spZ (ms_regs ms2) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
pose proof (count_cid_le_length 0 (frames S)) as Hcnt.
assert (Hfs0 : 16 <= fs_frames 0) by (vm_compute; intro Hq; discriminate Hq).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML (CmdRecRest.cmd_stack_malloc_progress B) 0 (ASTACK_MALLOC0 fx) ltac:(lia) W (ms_regs ms2) (ms_mem ms2)
    SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs) (getr (ms_regs ms2) 1) HJ);
  [ exact Qsp2 | rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity | lia | rewrite FS, Hes; lia
  | rewrite R3; exact Hgp | rewrite R4; exact Htp
  | reflexivity | rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity] | lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJs & (fS2 & ES2)).
rewrite R1.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & _).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply spcb_region_kept_hi; [exact U34 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia].
  - eapply spcb_region_kept_hi; [exact V2 | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 Qsp2.
remember (havoc E1 40 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall n, (n < 40)%nat -> ew E2 n = ew E1 n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (E44 : ew E2 44 = Z_to_bv 64 F).
{ rewrite HE2. change 44%nat with (40 + 4)%nat. rewrite (ew_havoc_new E1 40 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh). fold F in HF4096, HFceil, HFhigh.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HF64 & _ & _). fold F in HF64.
destruct (cmd_frame_flag_law B _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc 56 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity) ltac:(cbv; lia)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E2 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 56)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
assert (E56 : ew E3 56 = Z_to_bv 64 FL) by (rewrite HE3; exact (ew_havoc_new E2 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E57 : ew E3 57 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE3; exact (ew_havoc_new E2 56 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
clear HE3.
assert (E3_44 : ew E3 44 = Z_to_bv 64 F) by (rewrite OLD3 by lia; exact E44).
assert (E3_32 : ew E3 32 = Z_to_bv 64 SB) by (rewrite OLD3, OLD2, OLD1 by lia; exact E32).
assert (W2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3, OLD2 by lia; exact V2).
assert (W34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3, OLD2 by lia; exact U34).
assert (W44 : bv_unsigned (ew E3 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (W56 : bv_unsigned (ew E3 56) = FL) by (rewrite E56; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (W57 : bv_unsigned (ew E3 57) = SB + F / 8) by (rewrite E57; apply unsigned_lit_small; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact Ev ssv msv 44 (HPTR 6) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite W44; change (2 ^ 6) with 64; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_alias Ev _ msv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 44 0) (SLit 3)) (SOff 32 0)) (SOff 57 0) HS
    (shadow_decl_ok Ev 44 32 57 F SB E3_44 ltac:(lia) E3_32 E57)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
(* the frame's regions: its header (frame + 0 .. 24 written), its flag word (frame + 56, the flag's address) and its
   eight shadow bytes *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 44%nat) 0 32 0 24 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite W44; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite W44, W2, W34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 44%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 56 0))]) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite W44; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS Ev _ F 56 8 (SOff 56 0) FL); [rewrite spcb_off0; exact E56 | lia | lia |];
      exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite W44, W2, W34; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 57%nat) 0 8 0 8 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite W57; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS);
      replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      apply (proj1 (HFSpres o ltac:(lia))))
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite W57, W44, W2, W34; unfold SB; pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia));
      repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
(* run 3: 0x8bf3c .. 0x8bfd0: s2 = s8 := the frame (bnez taken), sp1's word, the frame's header and shadow, then
   a0 := 14 and the call of record *)
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact W57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact W44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite W34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite W2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.

(* ---- facts of the entry the calls use ---- *)
pose proof HREP as (Q0 & HQ0 & HOQ0).
pose proof HQ0 as (_ & _ & _ & (HC1 & _) & _).
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (spr_O_in ly S _ R O HREP).
assert (HOpos : forall pn, In pn O -> 0 < fst pn).
{ intros [b n] Hq. destruct (spr_blk_bounds ly S W mem md b n HAR (HOin _ Hq)) as (Hb & _). cbn. lia. }
assert (HFPlow : forall a, inFP FP a -> 0 <= a < alloc_ceiling)
  by (intros a Ha; exact (spr_FP_low ly S W mem md O a HAR HOin Ha)).
assert (HRS : RECORD_STK = 16560) by (vm_compute; reflexivity).
assert (HAS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HSS : REC_SHAPE_OF_STK = 8288) by (vm_compute; reflexivity).
assert (HNS : ANSWER_STK = 16592) by (vm_compute; reflexivity).
assert (XR0 : 0 <= XM_RECORD MT R).
{ unfold XM_RECORD, rec_spill_frees. pose proof (mo_free_nonneg MT MTL). destruct (Nat.ltb _ _); lia. }
assert (XA0 : forall v, 0 <= XM_ARG_S MT v).
{ intros v. unfold XM_ARG_S, XM_XMALLOC. apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
assert (XN0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length t) + 1)) ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (LN0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
assert (LA0 : forall v, 0 <= LIVE_ARG_S v) by (intros v; unfold LIVE_ARG_S, LIVE_XMALLOC; lia).
(* the meter at the frame's state S2 = set_fs _ S *)
assert (HMOK2 : mo_ok MT S2 (XM_SUP_POOL_CONFIG MT R name max)) by (rewrite ES2; exact (mo_ok_set_fs MT MTLF _ _ _ HMOK)).
assert (MLE2 : mo_le MT S S2 0) by (rewrite ES2; exact (mo_le_set_fs_r MT MTLF _ _ _ _ (mo_le_refl MT MTL S))).
(* ---- the record(14) call (0x8bfd0) ---- *)
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PA1. prreg HS (2%bv : bv 5) PA2. prreg HS (3%bv : bv 5) PA3. prreg HS (4%bv : bv 5) PA4.
prreg HS (8%bv : bv 5) PA8. prreg HS (10%bv : bv 5) PA10.
assert (EE3 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD3, OLD2, OLD1 by lia; exact (EE n r Hr)).
assert (GA2 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PA2, W34; lia).
assert (GA3 : getr (ms_regs ms3) 3 = w64 (as_gp B)) by (rewrite PA3, (EE3 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GA4 : getr (ms_regs ms3) 4 = w64 (as_tp B)) by (rewrite PA4, (EE3 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (GA8 : s0Z (ms_regs ms3) = spZ regs) by (unfold s0Z; rewrite PA8; exact W2).
assert (GA10 : getr (ms_regs ms3) 10 = w64 REC_POOL_CONFIG) by (rewrite PA10; reflexivity).
assert (GA1r : YK0s.ret_ok (getr (ms_regs ms3) 1)) by (rewrite PA1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GA1a : 4096 <= bv_unsigned (getr (ms_regs ms3) 1))
  by (rewrite PA1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* what runs 1-3 and __asan_stack_malloc_0 kept: every byte below alloc_ceiling outside the frame and its shadow *)
assert (KR1 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H W) mem (ms_mem ms1) (fun a => alloc_ceiling <= a) HFr1); [|lia|lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]). destruct Hin. }
assert (KR2 : forall a, 0 <= a < alloc_ceiling -> rdW W (ms_mem ms2) a = rdW W (ms_mem ms1) a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E1 _ (w_H W) (ms_mem ms1) (ms_mem ms2) (fun a => alloc_ceiling <= a) HFr2); [|lia|lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U34, ?V2 in Hrr; lia|]). destruct Hin. }
assert (KR3 : forall a, 0 <= a < alloc_ceiling -> ~ spcb_zf F a -> rdW W (ms_mem ms3) a = rdW W mem2 a).
{ intros a Ha Hzf. apply (kept_of_frame (segs := SEGS) E3 _ (w_H W) mem2 (ms_mem ms3) (fun a => alloc_ceiling <= a \/ spcb_zf F a) HFr3);
  [| lia | intros [Hq | Hq]; [lia | exact (Hzf Hq)]].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. unfold spcb_zf.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?W57, ?W44, ?W34, ?W2 in Hrr; lia|]).
  destruct Hin. }
assert (K3 : forall a, (Exists (in_zr a) TFIB_PROG_STATIC \/ exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) ->
  rdW W (ms_mem ms3) a = rdW W mem a).
{ intros a Ha.
  assert (Ha2 : Exists (in_zr a) TFIB_PROG_STATIC \/ exists b m, In (b, m) (ablocks B ly S2) /\ b <= a < b + req_size m)
    by (rewrite Eab; exact Ha).
  destruct (spcb_nzf ly S2 W mem2 md2 fpos a HAR2 Hfin2 Ha2) as [Hac Hnz]. fold F in Hnz.
  assert (Hq0 : 0 <= a).
  { destruct Ha as [HP | (b & m & Hbm & Hba)]; [pose proof (spr_static_low a HP); lia|].
    destruct (spr_blk_bounds ly S W mem md b m HAR Hbm). lia. }
  rewrite (KR3 a ltac:(lia) Hnz).
  destruct Ha as [HP | (b & m & Hbm & Hba)].
  - destruct ((recb_prog_unowned_m B HB cmd_prog_img) a HP) as (Hi & Ho & He). rewrite (HK3 a Hi Ho He). rewrite KR2, KR1 by lia. reflexivity.
  - replace a with (b + (a - b)) by lia. rewrite (HK2 b m (a - b) Hbm ltac:(lia) (fun H => H)). rewrite KR2, KR1 by lia. reflexivity. }
assert (HREPA : rec_repA B ly S2 (rdW W (ms_mem ms3)) R O).
{ apply (spr_rec_repA_ext ly S (rdW W mem) ly S2 _ R O HREP).
  - intros qn Hq. rewrite Eab. exact (HOin qn Hq).
  - intros a [Ha | [Ha | ([b n] & Hq & Ha)]]; cbn [fst snd] in *; apply K3.
    + left. exact (spr_grec_in a Ha).
    + left. exact (spr_spill_in a Ha).
    + right. exists b, n. split; [exact (HOin _ Hq)|].
      destruct (spr_blk_bounds ly S W mem md b n HAR (HOin _ Hq)) as (_ & _ & _ & Hnr & _). lia. }
assert (HROA : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3)))
  by exact (spr_aro ly S W mem md O ly S2 W (ms_mem ms3) _ [(0, fpos)] 0 (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ2 HROD).
(* the frame chain of s0 = the entry sp at the calls: afn_pre's chain pushed by the prologue's ra and s0 words *)
spcb_chunk HS 4%nat (-8) CW8. spcb_chunk HS 4%nat (-16) CW16.
assert (Hw8 : rdword (rdW W (ms_mem ms3)) (spZ regs - 8) = Some (raZ regs)).
{ apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (bv_unsigned (ew E3 2) + -8) by lia.
  apply CW8; [|unfold raZ; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE3 1%nat 1%bv ltac:(lia) eq_refl). unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hw16 : rdword (rdW W (ms_mem ms3)) (spZ regs - 16) = Some (s0Z regs)).
{ apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (bv_unsigned (ew E3 2) + -16) by lia.
  apply CW16; [|unfold s0Z; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE3 8%nat 8%bv ltac:(lia) eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
destruct (spcb_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs + (sp1 - spZ regs)) HJ2
  (fun a Ha => proj2 (HFPlow a Ha)) Hch Hw8 Hw16 Hra4 ltac:(lia)) as (ch1 & HCH1).

pose proof (frm_off_imgP B ly S2 W mem2 md2 0 fpos HAR2 Hfin2) as HoffF.
change (fs_frame_bytes 0) with 64 in HoffF. fold F in HoffF. unfold off_img in HoffF.
(* record's footprint: g_rec.ncalls, the slot's fn and nargs, and in the spill arm the recorder's blocks *)
assert (HFPR : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a -> a < alloc_ceiling /\ ~ spcb_zf F a).
{ intros a Ha. apply (spcb_fp_apart ly S2 W mem2 md2 fpos a HAR2 Hfin2).
  apply inFP_cons in Ha as [Ha | Ha]; [left; unfold A_G_REC, OFF_NCALLS, REC_SIZE in *; lia|].
  apply inFP_cons in Ha as [Ha | Ha].
  { destruct (spr_slot_bounds R HC1) as [Hs | Hs]; [left; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    right; left. rewrite Hs in Ha. unfold A_REC_SPILL, SC_SIZE in *. lia. }
  destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
  destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba). right; right.
  exists b, n. split; [rewrite Eab; exact (HOin _ Hbn) | exact Hba]. }
rewrite (rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) _ SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly S2 _ 0
    RECORD_STK _ (EV_RECORD R) (sp1 - spZ regs) (getr (ms_regs ms3) 1) ch1 _ HJ2 GA2
    ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
    ltac:(rewrite HRS; lia) ltac:(rewrite HRS, FS; lia) GA3 GA4 eq_refl GA1r GA1a ltac:(rewrite GA8; exact HCH1)).
  - intros HPRE1. pose proof (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch1 REC_POOL_CONFIG R O HPRE1) as T.
    unfold apost_base in T. apply T.
    + exact HROA.
    + exact GA10.
    + unfold REC_POOL_CONFIG, REC_FN_COUNT; lia.
    + exact HREPA.
    + rewrite Hnev2. unfold EV_SUP_POOL_CONFIG, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in HEV. lia.
    + apply (mo_ok_le MT MTL S2 _ _ HMOK2). unfold XM_SUP_POOL_CONFIG.
      pose proof (XA0 name). pose proof (XA0 (Some (dec max))). pose proof (XN0 (snd (sup_pool_config_m R name max))). lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha].
    { apply spr_awr_grec. unfold OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in Ha as [Ha | Ha].
    { apply (spr_awr_slot _ _ _ _ _ _ _ _ R a HC1). unfold CALL_SIZE. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exfalso; exact (inFP_nil a Ha)|].
    destruct (inFP_ablocks_fp_inv O a Ha) as (b & n & Hbn & Hba).
    apply (spr_awr_blk _ _ _ _ _ _ _ _ b n a Hbn); [rewrite Eab; exact (HOin _ Hbn) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. destruct (HFPR a Ha) as [Hlo _]. lia. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HKr).
destruct HKr as (Fr & O1 & R10 & HPermF & HFlen & HFO & HREP1 & HO1 & HBB1 & MLE1).
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & Hnev4 & _).
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
destruct (al_layout _ _ LAWS ly S W mem md ly4 HAR Hly4) as (_ & Efa4 & _).
rewrite PA1.
jafter_call_keep_pi HS 60%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3; 4]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc4 | exact W57 | exact Hfin2 | unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; lia
    | unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HFPR a HFa) as [_ Hzf]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly4 S4 W4 mem4 md4 0 fpos a HAR4 Hfin4); right; rewrite Efa4;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc4 | exact W44 | exact Hfin2 | fold F; lia | change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPR a HFa) as [_ Hzf]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc4 | exact W44 | exact Hfin2 | fold F; lia | change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPR a HFa) as [_ Hzf]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly4 S4 W4 mem4 md4 0 fpos a HAR4 Hfin4); left; rewrite Efa4;
      change (fs_frame_bytes 0) with 64; fold F; lia ].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc4 | exact HJ4 | exact W34 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPR a HFa) as [Hlo _]. cbn in Ha. lia.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc4 | exact HJ4 | exact W2 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPR a HFa) as [Hlo _]. cbn in Ha. lia. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
remember (havoc E3 60 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 60)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
assert (A64 : ew E4 64 = getr regs4 10).
{ rewrite HE4. change 64%nat with (60 + 4)%nat. rewrite (ew_havoc_new E3 60 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
assert (HAE4 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E4)
  by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4.
assert (X2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact W2).
assert (X34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact W34).
assert (X44 : bv_unsigned (ew E4 44) = F) by (rewrite OLD4 by lia; exact W44).
assert (X57 : bv_unsigned (ew E4 57) = SB + F / 8) by (rewrite OLD4 by lia; exact W57).
assert (EE4 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD4 by lia; exact (EE3 n r Hn Hr)).
(* ---- run 4: 0x8bfd4 .. 0x8bfdc: s6 := the slot, a1 := name, the call of arg_s ---- *)
paj_run_shc RUNP RUNC HS HJ4.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact X57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa4; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact X44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite Efa4; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite X34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite X2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms4, mat into mat4, HF into HF4, HFr into HFr4, HG into HG4.
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PB1. prreg HS (2%bv : bv 5) PB2. prreg HS (3%bv : bv 5) PB3. prreg HS (4%bv : bv 5) PB4.
prreg HS (8%bv : bv 5) PB8. prreg HS (10%bv : bv 5) PB10. prreg HS (11%bv : bv 5) PB11.
assert (GB2 : spZ (ms_regs ms4) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PB2, X34; lia).
assert (GB3 : getr (ms_regs ms4) 3 = w64 (as_gp B)) by (rewrite PB3, (EE4 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GB4 : getr (ms_regs ms4) 4 = w64 (as_tp B)) by (rewrite PB4, (EE4 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (GB8 : s0Z (ms_regs ms4) = spZ regs) by (unfold s0Z; rewrite PB8; exact X2).
assert (GB10 : getr (ms_regs ms4) 10 = w64 (rec_slot R)) by (rewrite PB10, A64; exact R10).
assert (GB11 : getr (ms_regs ms4) 11 = w64 pn) by (rewrite PB11, (EE4 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (GB1r : YK0s.ret_ok (getr (ms_regs ms4) 1)) by (rewrite PB1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GB1a : 4096 <= bv_unsigned (getr (ms_regs ms4) 1))
  by (rewrite PB1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* run 4 wrote no byte below alloc_ceiling outside the frame and its shadow *)
assert (KB : forall a, 0 <= a < alloc_ceiling -> ~ spcb_zf F a -> rdW W4 (ms_mem ms4) a = rdW W4 mem4 a).
{ intros a Ha Hzf. apply (kept_of_frame (segs := SEGS) E4 _ (w_H W4) mem4 (ms_mem ms4) (fun a => alloc_ceiling <= a \/ spcb_zf F a) HFr4);
  [| lia | intros [Hq | Hq]; [lia | exact (Hzf Hq)]].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. unfold spcb_zf.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?X57, ?X44, ?X34, ?X2 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ4) as HAR4b.
assert (HO1in : forall qn, In qn O1 -> In qn (ablocks B ly4 S4)) by exact (spr_O_in ly4 S4 _ _ O1 HREP1).
assert (HFP4 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  exists b m, In (b, m) (ablocks B ly4 S4) /\ b <= a < b + req_size m) -> a < alloc_ceiling /\ ~ spcb_zf F a).
{ intros a Ha. pose proof (spcb_fp_apart ly4 S4 W4 mem4 md4 fpos a HAR4 Hfin4 Ha) as Hq. rewrite Efa4 in Hq. exact Hq. }
assert (HREPB : rec_repA B ly4 S4 (rdW W4 (ms_mem ms4)) (rec_record R REC_POOL_CONFIG []) O1).
{ apply (spr_rec_repA_ext ly4 S4 (rdW W4 mem4) ly4 S4 _ _ O1 HREP1 HO1in).
  intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    exists b m, In (b, m) (ablocks B ly4 S4) /\ b <= a < b + req_size m).
  { destruct Ha as [Ha | [Ha | ([b m] & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha|].
    right; right. exists b, m. split; [exact (HO1in _ Hq)|]. cbn [fst snd] in Ha.
    destruct (spr_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 (HO1in _ Hq)) as (_ & _ & _ & Hm & _). lia. }
  destruct (HFP4 a Ha') as [Hlo Hzf].
  assert (Hq0 : 0 <= a).
  { destruct Ha' as [Hq | [Hq | (b & m & Hbm & Hba)]]; [unfold A_G_REC in Hq; lia | unfold A_REC_SPILL in Hq; lia|].
    destruct (spr_blk_bounds ly4 S4 W4 mem4 md4 b m HAR4 Hbm). lia. }
  exact (KB a ltac:(lia) Hzf). }
assert (HROB : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms4)))
  by exact (spr_aro ly S W mem md O ly4 S4 W4 (ms_mem ms4) _ [(0, fpos)] _ (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ4 HROD).
assert (HROkB : cmd_ro_ok (rdW W4 (ms_mem ms4))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR4b HROB).
(* the name argument: a heap string of a block that is none of the recorder's; its bytes and word tail are kept *)
destruct HNAME as (x & -> & Hblk & Hstr & Hlenx & Hapx).
assert (HlivB : forall qn, In qn (ablocks B ly S) -> ~ In qn O -> In qn (ablocks B ly4 S4)).
{ intros qn Hq HnO. rewrite <- Eab in Hq. apply (Permutation_in _ HPermF) in Hq. apply in_app_or in Hq as [Hq | Hq]; [exact Hq|].
  exfalso. exact (HnO (HFO _ Hq)). }
assert (HbytB : forall b k a, In (b, k) (ablocks B ly S) -> ~ In (b, k) O -> b <= a < b + k ->
  rdW W4 (ms_mem ms4) a = rdW W mem a).
{ intros b k a Hbk HnO Ha. pose proof (HlivB _ Hbk HnO) as Hbk4.
  destruct (spr_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & Hbc & Hk0 & Hkr & _).
  destruct (HFP4 a ltac:(right; right; exists b, k; split; [exact Hbk4 | lia])) as [Hlo Hzf].
  rewrite (KB a ltac:(lia) Hzf).
  replace a with (b + (a - b)) by lia.
  rewrite (spr_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b k (a - b) HJc4 ltac:(rewrite Eab; exact Hbk) Hbk4 ltac:(lia)).
  - apply K3. right. exists b, k. split; [exact Hbk | lia].
  - intros HFa. apply inFP_cons in HFa as [HFa | HFa].
    { apply (spr_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. apply spr_grec_in. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia. }
    apply inFP_cons in HFa as [HFa | HFa].
    { apply (spr_blk_noimg ly S W mem md b k (b + (a - b)) HAR Hbk ltac:(lia)).
      apply cmd_prog_img. destruct (spr_slot_bounds R HC1) as [Hs | Hs].
      - apply spr_grec_in. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *. lia.
      - apply spr_spill_in. rewrite Hs in HFa. unfold A_REC_SPILL, SC_SIZE in *. lia. }
    destruct (Nat.ltb (length (r_calls R)) 16); [exact (inFP_nil _ HFa)|].
    destruct (inFP_ablocks_fp_inv O _ HFa) as (b' & n' & Hbn & Hba).
    destruct (spr_pair_dec (b, k) (b', n')) as [Eq | Hne]; [apply HnO; rewrite Eq; exact Hbn|].
    destruct (spr_blk_bounds ly S W mem md b' n' HAR (HOin _ Hbn)) as (_ & _ & _ & Hnr' & _).
    destruct (spr_blk_apart ly S W mem md b k b' n' HAR Hbk (HOin _ Hbn) Hne); lia. }
assert (HargA0 : astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O pn (Some x)).
{ cbn [astr_argA]. destruct Hblk as (b & k & Hbk & Hble & Hhi).
  destruct (spr_blk_bounds ly S W mem md b k HAR Hbk) as (Hb & _).
  split; [lia|]. split; [exact Hstr|]. split; [exact Hlenx|]. left. split; [exists b, k; auto | exact Hapx]. }
assert (Htl0 : atail_vis SEGS W mem (pn + Z.of_nat (length x))).
{ destruct Hblk as (b & k & Hbk & Hble & Hhi).
  destruct (spr_blk_bounds ly S W mem md b k HAR Hbk) as (_ & _ & _ & Hkr & _).
  exact (cmd_heap_tail_vis ly S W mem md b k (pn + Z.of_nat (length x)) HAR Hbk ltac:(lia)). }
destruct (spr_arg_kept ly S W mem md ly4 S4 W4 (ms_mem ms4) _ O pn x HAR HAR4b HROD HROB HlivB HbytB HargA0 Htl0)
  as (HargB & HtlB).
(* the chain and the call of arg_s(slot, name) (0x8bfdc) *)
spcb_chunk HS 4%nat (-8) CB8. spcb_chunk HS 4%nat (-16) CB16.
assert (Hw8b : rdword (rdW W4 (ms_mem ms4)) (spZ regs - 8) = Some (raZ regs)).
{ apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (bv_unsigned (ew E4 2) + -8) by lia.
  apply CB8; [|unfold raZ; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE4 1%nat 1%bv ltac:(lia) eq_refl). unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hw16b : rdword (rdW W4 (ms_mem ms4)) (spZ regs - 16) = Some (s0Z regs)).
{ apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (bv_unsigned (ew E4 2) + -16) by lia.
  apply CB16; [|unfold s0Z; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE4 8%nat 8%bv ltac:(lia) eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
destruct (spcb_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs + (sp1 - spZ regs)) HJ4
  (fun a Ha => proj2 (HFPlow a Ha)) Hch Hw8b Hw16b Hra4 ltac:(lia)) as (ch2 & HCH2).
assert (HFPA : forall a, inFP (if Z.of_nat (length ([] : list (list byte))) <? REC_ARGS_MAX
    then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
          (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))),
           rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length ([] : list (list byte))) + 8)]
    else []) a -> a < alloc_ceiling /\ ~ spcb_zf F a /\ rec_slot R <= a < rec_slot R + CALL_SIZE).
{ intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
  assert (Hsl : rec_slot R <= a < rec_slot R + CALL_SIZE).
  { apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exfalso; exact (inFP_nil a Ha)]. }
  destruct (spcb_fp_apart ly S2 W mem2 md2 fpos a HAR2 Hfin2) as [Hlo Hzf].
  { destruct (spr_slot_bounds R HC1) as [Hs | Hs]; [left; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    right; left. rewrite Hs in Hsl. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
  split; [exact Hlo|]. split; [exact Hzf | exact Hsl]. }
rewrite spcb_sig_arg_s.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W4 (ms_regs ms4) (ms_mem ms4) _ SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly4 S4 _ _
    ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms4) 1) ch2 _ HJ4 GB2
    ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, FS; lia) GB3 GB4 eq_refl GB1r GB1a ltac:(rewrite GB8; exact HCH2)).
  - intros HPRE1. pose proof (TARG_S fx ly4 S4 W4 (ms_regs ms4) (ms_mem ms4) _ ch2 (rec_slot R) pn REC_POOL_CONFIG []
      (Some x) R O1 HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROB.
    + exact HROkB.
    + exact GB10.
    + exact GB11.
    + reflexivity.
    + exact HREPB.
    + left. exact HargB.
    + intros x0 Hx0. injection Hx0 as <-. exact HtlB.
    + pose proof HJ4 as (_ & _ & _ & _ & _ & _ & Hnv & _).
      unfold EV_SUP_POOL_CONFIG, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + rewrite Hbb2 in HBB1. pose proof (LA0 (Some (dec max))). pose proof (LN0 (snd (sup_pool_config_m R (Some x) max))).
      unfold LIVE_SUP_POOL_CONFIG in HLIVE. lia.
    + apply (mok_station MT S2 S4 (XM_SUP_POOL_CONFIG MT R (Some x) max) (XM_RECORD MT R) _ MTL HMOK2 MLE1 (XA0 _)).
      unfold XM_SUP_POOL_CONFIG. pose proof (XA0 (Some (dec max))). pose proof (XN0 (snd (sup_pool_config_m R (Some x) max))). lia.
  - intros a Ha. destruct (HFPA a Ha) as (_ & _ & Hsl). exact (spr_awr_slot _ _ _ _ _ _ _ _ R a HC1 Hsl).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. destruct (HFPA a Ha) as [Hlo _]. lia. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HKa).
destruct HKa as (HBB5 & MLE5 & [(Hc6 & _) | (_ & p1 & Hp1 & Hperm5 & Hfresh5 & HREP5)]).
{ exfalso. unfold REC_ARGS_MAX in Hc6. cbn [length Z.of_nat] in Hc6. lia. }
cbn [app] in HREP5.
pose proof (proj1 HJ5) as HAR5.
pose proof HJ5 as (_ & Hly5 & _ & _ & _ & Hfrs5 & Hnev5 & _).
assert (Hfin5 : In (0, fpos) (frames S5)) by (rewrite Hfrs5; left; reflexivity).
destruct (al_layout _ _ LAWS ly S W mem md ly5 HAR Hly5) as (_ & Efa5 & _).
rewrite PB1.
jafter_call_keep_pi HS 80%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0; 1; 2; 3; 4]%nat HS5.
match type of HS5 with ?tq -> _ => assert (HRK : tq); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc5 | exact X57 | exact Hfin4 | unfold shadow_addr; rewrite ?Efa4; rewrite <- SB_SHADOW_OFF; fold F; lia
    | unfold shadow_addr; rewrite ?Efa4; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HFPA a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly5 S5 W5 mem5 md5 0 fpos a HAR5 Hfin5); right; rewrite Efa5;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc5 | exact X44 | exact Hfin4 | rewrite ?Efa4; fold F; lia | rewrite ?Efa4; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPA a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc5 | exact X44 | exact Hfin4 | rewrite ?Efa4; fold F; lia | rewrite ?Efa4; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPA a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly5 S5 W5 mem5 md5 0 fpos a HAR5 Hfin5); left; rewrite Efa5;
      change (fs_frame_bytes 0) with 64; fold F; lia ].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc5 | exact HJ5 | exact X34 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPA a HFa) as [Hlo _]. cbn in Ha. lia.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc5 | exact HJ5 | exact X2 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPA a HFa) as [Hlo _]. cbn in Ha. lia. }
rewrite <- restrict_mkst_fx in HS5. clear HS. rename HS5 into HS.
remember (havoc E4 80 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall n, (n < 80)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
assert (HAE5 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E5)
  by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5.
assert (Y2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact X34).
assert (Y44 : bv_unsigned (ew E5 44) = F) by (rewrite OLD5 by lia; exact X44).
assert (Y57 : bv_unsigned (ew E5 57) = SB + F / 8) by (rewrite OLD5 by lia; exact X57).
assert (EE5 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E5 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD5 by lia; exact (EE4 n r Hn Hr)).
(* ---- run 5: 0x8bfe0 .. 0x8bffc: b's shadow := 00 00, a0 := b, a1 := 16, a2 := "%d", a3 := max, the call of the
   snprintf wrapper ---- *)
paj_run_shc RUNP RUNC HS HJ5.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact Y57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa5; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact Y44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite Efa5; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Y34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Y2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms6, mat into mat6, HF into HF6, HFr into HFr6, HG into HG6.
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PC1. prreg HS (2%bv : bv 5) PC2. prreg HS (3%bv : bv 5) PC3. prreg HS (4%bv : bv 5) PC4.
prreg HS (10%bv : bv 5) PC10. prreg HS (11%bv : bv 5) PC11. prreg HS (12%bv : bv 5) PC12. prreg HS (13%bv : bv 5) PC13.
(* ---- the snprintf(b, 16, "%d", max) call (0x8bffc): a Theorem Labs lane's shared contract through PaFx's art step ---- *)
assert (GC2 : spZ (ms_regs ms6) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PC2, Y34; lia).
assert (GC3 : getr (ms_regs ms6) 3 = w64 (as_gp B)) by (rewrite PC3, (EE5 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GC4 : getr (ms_regs ms6) 4 = w64 (as_tp B)) by (rewrite PC4, (EE5 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (GC10 : getr (ms_regs ms6) 10 = w64 (F + 32)) by (rewrite PC10, Y44; reflexivity).
assert (GC11 : getr (ms_regs ms6) 11 = w64 16) by (rewrite PC11; reflexivity).
assert (VF : VAL (A_OBJ 51) = 0x21f40) by (rewrite (VOBJS 51%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (GC12 : getr (ms_regs ms6) 12 = w64 0x21f40).
{ rewrite PC12. change 292%nat with (A_OBJ 51).
  rewrite (img_env_atomP E5 (A_OBJ 51) HEI5 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), VF. reflexivity. }
assert (GC13 : getr (ms_regs ms6) 13 = w64 max) by (rewrite PC13, (EE5 11%nat 11%bv ltac:(lia) eq_refl); exact H11).
pose proof (proj1 HJ5) as HAR6.
pose proof HJ5 as (_ & Hly6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres6 & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop6 & Eslo6 & Eshi6 & _).
assert (HROC : arodata_okP SEGS RLO RHI B (rdW W5 (ms_mem ms6)))
  by exact (spr_aro ly S W mem md O ly5 S5 W5 (ms_mem ms6) _ [(0, fpos)] _ (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ5 HROD).
assert (HROkC : cmd_ro_ok (rdW W5 (ms_mem ms6))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR6 HROC).
destruct (cmd_rec_cells ly5 S5 W5 (ms_mem ms6) _ HAR6) as (_ & (Hg1 & cval & Hg2) & _).
spcb_chunk HS 0%nat 4 SH4. spcb_chunk HS 0%nat 5 SH5.
set (Tt := PF.pf_dec max).
pose proof (spcb_pf_dec_len max Hmax) as HTl. fold Tt in HTl.
assert (Hsn : sn_len (16 - 1) Tt = Z.of_nat (length Tt) + 1).
{ unfold sn_len, sn_bytes. rewrite length_app, firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia). cbn [length]. lia. }
assert (Hsb : sn_bytes (16 - 1) Tt = Tt ++ [0]).
{ unfold sn_bytes. rewrite firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia). reflexivity. }
assert (HbF : F mod 64 = 0) by (pose proof (Z.div_mod F 64 ltac:(lia)); pose proof (Z.mod_pos_bound F 64 ltac:(lia)); lia).
assert (HSB4 : rdW W5 (ms_mem ms6) (SB + F / 8 + 4) = Some 0).
{ apply (spcb_aview_val1 SEGS (w_H W5) (ms_mem ms6)); [|lia]. rewrite <- Y57.
  apply SH4; [reflexivity | cbn; lia | cbn; lia]. }
assert (HSB5 : rdW W5 (ms_mem ms6) (SB + F / 8 + 5) = Some 0).
{ apply (spcb_aview_val1 SEGS (w_H W5) (ms_mem ms6)); [|lia]. rewrite <- Y57.
  apply SH5; [reflexivity | cbn; lia | cbn; lia]. }
destruct (spcb_b_shadow (rdW W5 (ms_mem ms6)) F (sn_len (16 - 1) Tt) HbF ltac:(lia) ltac:(rewrite Hsn; lia) HSB4 HSB5)
  as [HRAb HHVb].
{ intros s Hs. apply crf_present_view. apply (spcb_frame_pres ly5 S5 W5 (ms_mem ms6) _ 0 fpos s HAR6 Hfin5).
  right. rewrite Efa5. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. fold F. change (fs_frame_bytes 0 / 8) with 8. lia. }
assert (Hscr : forall a, spZ (ms_regs ms6) - CMD_SNP_K <= a < spZ (ms_regs ms6) -> apresent (w_H W5) (ms_mem ms6) a).
{ intros a Ha. apply Hpres6. rewrite GC2 in Ha. unfold CMD_SNP_K in Ha. rewrite FS. lia. }
assert (A3 : argZ (ms_regs ms6) 3 = bv_unsigned (getr (ms_regs ms6) 13)) by reflexivity.
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low CMD_SNP_K (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) Tt) _ W5
    (ms_regs ms6) (ms_mem ms6) SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly5 S5 _ _ (sp1 - spZ regs)
    (getr (ms_regs ms6) 1) _ HJ5 GC2 ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
    ltac:(unfold CMD_SNP_K; lia) ltac:(unfold CMD_SNP_K; rewrite FS; lia) eq_refl).
  - intros a Ha. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite Efa5. fold F. change (fs_frame_bytes 0) with 64. rewrite Hsn in Ha. lia.
  - apply (srr_art_postF_of_pf SEGS B CMD_SNP_K ly5 S5 W5 (ms_regs ms6) (ms_mem ms6) _ _ (F + 32) (sn_len (16 - 1) Tt)
      (sn_bytes (16 - 1) Tt) (Z.of_nat (length Tt)) Hscr).
    apply (ASNPRINTF fx ly5 S5 W5 (ms_regs ms6) (ms_mem ms6) _ (F + 32) 16 0x21f40 []
      (map (argZ (ms_regs ms6)) [3; 4; 5; 6; 7]) Tt cval).
    + exact (ecall_pre_at SEGS B SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly5 S5 W5 (ms_mem ms6) _ _
        (ms_regs ms6) (sp1 - spZ regs) HJ5 GC2 ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
        ltac:(rewrite FS, Hes; lia) ltac:(rewrite PC1; apply ret_ok_codeptr_v; [lia | reflexivity]) GC3 GC4).
    + rewrite GC2, Eslo6. unfold CMD_SNP_K. rewrite Hes. lia.
    + exact Hscr.
    + exact GC10.
    + exact GC11.
    + exact GC12.
    + exact (cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG RLO RHI W5 (ms_mem ms6) HROC).
    + exact spcb_cr_bnd.
    + apply spcb_cr_disj; [rewrite GC2; unfold CMD_SNP_K; rewrite Hes; lia | unfold CMD_SNP_K; rewrite Hes; lia | rewrite Hsn; lia | rewrite Hsn; lia].
    + exact Hg1.
    + exact Hg2.
    + lia.
    + lia.
    + lia.
    + lia.
    + unfold snp_out. rewrite GC2, Hsn. unfold CMD_SNP_K. rewrite Hes. spcb_fz.
    + unfold snp_out. rewrite GC2, Hsn. unfold CMD_SNP_K. rewrite Hes. spcb_fz.
    + split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn in Hi; lia].
    + cbn [length Z.of_nat]. rewrite GC2. lia.
    + unfold snp_out. rewrite GC2, Hsn. unfold CMD_SNP_K. rewrite Hes. cbn [length Z.of_nat].
      spcb_fz.
    + apply (FR_cmd_intro _ _ 0x21f40 _ Tt spcb_fmt [PF.Pd] [PF.AInt max]).
      * split; [lia|]. split; [exact (spcb_fmt_bytes _ HROkC)|].
        split; [unfold snp_out; rewrite GC2, Hsn; unfold CMD_SNP_K; rewrite Hes; cbn [length spcb_fmt Z.of_nat];
                spcb_fz|].
        split; [left; unfold kLowMemEnd; cbn; lia|].
        split; [exact (spcb_addressable_chk SEGS B LAWS HB ly5 S5 W5 (ms_mem ms6) _ 0x21f40 3 HAR6 (proj1 spcb_fmt_chk))|].
        exact (spcb_hull_vis_chk SEGS B LAWS HB ly5 S5 W5 (ms_mem ms6) _ 0x21f40 3 HAR6 (proj2 spcb_fmt_chk)).
      * exact spcb_fmt_parse.
      * cbn [map arg_of pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hmax|].
        rewrite A3, GC13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite (Z.mod_eq max (2 ^ 64)) by lia.
        replace (max - 2 ^ 64 * (max / 2 ^ 64)) with (max + (- (2 ^ 32) * (max / 2 ^ 64)) * 2 ^ 32) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      * exact (snt_text_d max).
      * cbn. exact I.
      * (* fr_lit_ok: "%d" at 0x21f40 is a nonempty literal below the GOT word, with no string argument *)
        vm_compute. reflexivity.
    + lia.
    + fold Tt in HTl. lia.
    + lia.
    + rewrite Hsn. lia.
    + unfold snp_out. rewrite GC2, Hsn. unfold CMD_SNP_K. rewrite Hes. cbn [pairwise].
      split; [spcb_fz | split; [apply Forall_nil | exact I]].
    + intros a Ha. rewrite Hsn in Ha. split; [|split].
      * apply (apresent_writable SEGS). apply (spcb_frame_pres ly5 S5 W5 (ms_mem ms6) _ 0 fpos a HAR6 Hfin5).
        left. rewrite Efa5. fold F. change (fs_frame_bytes 0) with 64. lia.
      * intros [_ Hc]. apply Hc. right. exists (0, fpos). split; [exact Hfin5|]. left. unfold in_zr. cbn [fst snd].
        rewrite Efa5. fold F. change (fs_frame_bytes 0) with 64. lia.
      * rewrite GC2. lia.
    + (* amem_range b (|dec max| + 1 + 8): b = frame + 32, so the 8 slack bytes stay in the 64-byte fake frame *)
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. rewrite Hsn. lia.
    + exact HRAb.
    + exact HHVb.
    + unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd]. rewrite Hsn. lia.
    + exact HFRM. }
intros fx1 regs7 mem7 md7 Hfx (HJ7 & HP7 & (HQ10 & HQby) & HK7).
(* ---- after the snprintf wrapper, at its FP state fx1: b holds "dec max" and its terminator ---- *)
pose proof (proj1 HJ7) as HAR7.
pose proof (Z.div_mod F 8 ltac:(lia)) as D8F. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8F.
pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Ems6. rewrite Ems6 in HS. clear Ems6.
lazymatch type of HS with @st_ok ?sg _ ?Ex ?ssx (restrict ?Hx (@mkst _ ?r ?p ?m ?ro)) =>
  pose proof (st_ok_restrict_xfx fx fx1 sg Ex ssx Hx _ HS ltac:(vm_compute; reflexivity)
    : @st_ok sg fx1 Ex ssx (restrict Hx (@mkst fx1 r p m ro))) as HSf end. clear HS. rename HSf into HS.
rewrite PC1.
jafter_call_keep_pi HS 100%nat regs7 (mrestrict (w_H W5) mem7) HP7 [0; 1; 2; 3; 4]%nat HS7.
match type of HS7 with ?tq -> _ => assert (HRK : tq); [|specialize (HS7 HRK); clear HRK] end.
{ pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres7 & _).
  cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply spcb_region_kept_hi; [exact Y57 | intros a Ha; apply HK7; cbv beta; [lia | lia | rewrite Hsn; lia]
    | intros a Ha; apply (spcb_frame_pres ly5 S5 W5 mem7 md7 0 fpos a HAR7 Hfin5); right; rewrite Efa5;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia].
  - eapply spcb_region_kept_hi; [exact Y44 | intros a Ha; apply HK7; cbv beta; [lia | lia | rewrite Hsn; lia] | intros a Ha; lia].
  - eapply spcb_region_kept_hi; [exact Y44 | intros a Ha; apply HK7; cbv beta; [lia | lia | rewrite Hsn; lia]
    | intros a Ha; apply (spcb_frame_pres ly5 S5 W5 mem7 md7 0 fpos a HAR7 Hfin5); left; rewrite Efa5; fold F;
      change (fs_frame_bytes 0) with 64; lia].
  - eapply spcb_region_kept_hi; [exact Y34 | intros a Ha; apply HK7; cbv beta; [lia | lia | rewrite Hsn; lia]
    | intros a Ha; apply Hpres7; rewrite FS; lia].
  - eapply spcb_region_kept_hi; [exact Y2 | intros a Ha; apply HK7; cbv beta; [lia | lia | rewrite Hsn; lia]
    | intros a Ha; apply Hpres7; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS7. clear HS. rename HS7 into HS.
remember (havoc E5 100 (map (getr regs7) CLOB)) as E7 eqn:HE7 in HS.
assert (HEI7 : img_env VAL A_LIM E7) by (rewrite HE7; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (OLD7 : forall n, (n < 100)%nat -> ew E7 n = ew E5 n) by (intros n Hn; rewrite HE7; apply ew_havoc_old; exact Hn).
assert (HAE7 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E7)
  by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE7.
assert (Z2 : bv_unsigned (ew E7 2) = spZ regs) by (rewrite OLD7 by lia; exact Y2).
assert (Z34 : bv_unsigned (ew E7 34) = sp1) by (rewrite OLD7 by lia; exact Y34).
assert (Z44 : bv_unsigned (ew E7 44) = F) by (rewrite OLD7 by lia; exact Y44).
assert (Z57 : bv_unsigned (ew E7 57) = SB + F / 8) by (rewrite OLD7 by lia; exact Y57).
assert (EE7 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E7 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD7 by lia; exact (EE5 n r Hn Hr)).
assert (Z64 : ew E7 64 = w64 (rec_slot R)) by (rewrite OLD7, OLD5 by lia; rewrite A64; exact R10).
(* ---- run 6: 0x8c000 .. 0x8c008: a0 := the slot, a1 := b, the call of arg_s (at fx1) ---- *)
pose proof (SRr_run_pi_AJ (fx := fx1) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNP1.
pose proof (SRr_run_pi_AJ_call (fx := fx1) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS) as RUNC1.
paj_run_shc RUNP1 RUNC1 HS HJ7.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact Z57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa5; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact Z44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite Efa5; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Z34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Z2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms8, mat into mat8, HF into HFq8, HFr into HFr8, HG into HG8.
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PD1. prreg HS (2%bv : bv 5) PD2. prreg HS (3%bv : bv 5) PD3. prreg HS (4%bv : bv 5) PD4.
prreg HS (8%bv : bv 5) PD8. prreg HS (10%bv : bv 5) PD10. prreg HS (11%bv : bv 5) PD11.
assert (GD2 : spZ (ms_regs ms8) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PD2, Z34; lia).
assert (GD3 : getr (ms_regs ms8) 3 = w64 (as_gp B)) by (rewrite PD3, (EE7 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GD4 : getr (ms_regs ms8) 4 = w64 (as_tp B)) by (rewrite PD4, (EE7 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (GD8 : s0Z (ms_regs ms8) = spZ regs) by (unfold s0Z; rewrite PD8; exact Z2).
assert (GD10 : getr (ms_regs ms8) 10 = w64 (rec_slot R)) by (rewrite PD10; exact Z64).
assert (GD11 : getr (ms_regs ms8) 11 = w64 (F + 32)) by (rewrite PD11, Z44; reflexivity).
assert (GD1r : YK0s.ret_ok (getr (ms_regs ms8) 1)) by (rewrite PD1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GD1a : 4096 <= bv_unsigned (getr (ms_regs ms8) 1))
  by (rewrite PD1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* what runs 5 and 6 kept: every byte outside the frame header's window, the frame's shadow and the stack *)
assert (KC5 : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 24) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
  rdW W5 (ms_mem ms6) a = rdW W5 mem5 a).
{ intros a Ha H1 H2. apply (kept_of_frame (segs := SEGS) E5 _ (w_H W5) mem5 (ms_mem ms6)
    (fun a => alloc_ceiling <= a \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 8) HFr6); [| lia | lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Y57, ?Y44, ?Y34, ?Y2 in Hrr; lia|]).
  destruct Hin. }
assert (KD : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 24) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
  rdW W5 (ms_mem ms8) a = rdW W5 mem7 a).
{ intros a Ha H1 H2. apply (kept_of_frame (segs := SEGS) E7 _ (w_H W5) mem7 (ms_mem ms8)
    (fun a => alloc_ceiling <= a \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 8) HFr8); [| lia | lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Z57, ?Z44, ?Z34, ?Z2 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ7) as HAR8.
(* the recorder at the arg_s call: rec_repA moved from arg_s's return (mem5) over runs 5, 6 and the snprintf *)
assert (HO5in : forall qn, In qn ((p1, Z.of_nat (length (sarg (Some x))) + 1) :: O1) -> In qn (ablocks B ly5 S5))
  by exact (spr_O_in ly5 S5 _ _ _ HREP5).
assert (HFP5 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  exists b m, In (b, m) (ablocks B ly5 S5) /\ b <= a < b + req_size m) -> 0 <= a < alloc_ceiling /\ ~ spcb_zf F a).
{ intros a Ha. pose proof (spcb_fp_apart ly5 S5 W5 mem5 md5 fpos a HAR5 Hfin5 Ha) as Hq. rewrite Efa5 in Hq.
  destruct Hq as [Hq1 Hq2]. split; [|exact Hq2].
  destruct Ha as [Hq | [Hq | (b & m & Hbm & Hba)]]; [unfold A_G_REC in Hq; lia | unfold A_REC_SPILL in Hq; lia|].
  destruct (spr_blk_bounds ly5 S5 W5 mem5 md5 b m HAR5 Hbm). lia. }
assert (K85 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  exists b m, In (b, m) (ablocks B ly5 S5) /\ b <= a < b + req_size m) -> rdW W5 (ms_mem ms8) a = rdW W5 mem5 a).
{ intros a Ha. destruct (HFP5 a Ha) as [Hlo Hzf]. unfold spcb_zf in Hzf.
  rewrite (KD a Hlo ltac:(lia) ltac:(lia)).
  rewrite (HK7 a ltac:(lia) ltac:(lia) ltac:(rewrite Hsn; lia)).
  exact (KC5 a Hlo ltac:(lia) ltac:(lia)). }
assert (HREPD : rec_repA B ly5 S5 (rdW W5 (ms_mem ms8)) (rec_record R REC_POOL_CONFIG [sarg (Some x)])
  ((p1, Z.of_nat (length (sarg (Some x))) + 1) :: O1)).
{ apply (spr_rec_repA_ext ly5 S5 (rdW W5 mem5) ly5 S5 _ _ _ HREP5 HO5in).
  intros a Ha. apply K85. destruct Ha as [Ha | [Ha | ([b m] & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha|].
  right; right. exists b, m. split; [exact (HO5in _ Hq)|]. cbn [fst snd] in Ha.
  destruct (spr_blk_bounds ly5 S5 W5 mem5 md5 b m HAR5 (HO5in _ Hq)) as (_ & _ & _ & Hm & _). lia. }
assert (HROD8 : arodata_okP SEGS RLO RHI B (rdW W5 (ms_mem ms8)))
  by exact (spr_aro ly S W mem md O ly5 S5 W5 (ms_mem ms8) _ [(0, fpos)] _ (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ7 HROD).
assert (HROk8 : cmd_ro_ok (rdW W5 (ms_mem ms8))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR8 HROD8).
(* the string at b *)
assert (Hstrb : astr_atR (rdW W5 (ms_mem ms8)) (F + 32) (dec max)).
{ rewrite <- (snt_pf_dec max Hmax). fold Tt. apply spcb_str_of_pf.
  - intros i Hi. rewrite (KD (F + 32 + i) ltac:(lia) ltac:(lia) ltac:(unfold SB in *; lia)).
    rewrite <- Hsb. apply HQby. rewrite Hsn. exact Hi.
  - intros a z Hzz. destruct (aview_byte SEGS _ _ _ _ Hzz) as (b0 & _ & _ & Hrg). exact Hrg.
  - unfold Tt. rewrite (snt_pf_dec max Hmax). exact (dec_no0 max). }
spcb_chunk HS 0%nat 4 SD4. spcb_chunk HS 0%nat 5 SD5.
assert (HSD4 : rdW W5 (ms_mem ms8) (SB + F / 8 + 4) = Some 0).
{ apply (spcb_aview_val1 SEGS (w_H W5) (ms_mem ms8)); [|lia]. rewrite <- Z57.
  apply SD4; [reflexivity | cbn; lia | cbn; lia]. }
assert (HSD5 : rdW W5 (ms_mem ms8) (SB + F / 8 + 5) = Some 0).
{ apply (spcb_aview_val1 SEGS (w_H W5) (ms_mem ms8)); [|lia]. rewrite <- Z57.
  apply SD5; [reflexivity | cbn; lia | cbn; lia]. }
pose proof (dec_length max Hmax) as Hdl.
destruct (spcb_b_shadow (rdW W5 (ms_mem ms8)) F (Z.of_nat (length (dec max)) + 1) HbF ltac:(lia) ltac:(lia) HSD4 HSD5)
  as [HRAd _].
{ intros s Hs. apply crf_present_view. apply (spcb_frame_pres ly5 S5 W5 (ms_mem ms8) _ 0 fpos s HAR8 Hfin5).
  right. rewrite Efa5. unfold shadow_addr. rewrite <- SB_SHADOW_OFF. fold F. change (fs_frame_bytes 0 / 8) with 8. lia. }
assert (HF64q : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (Hafobj : afobj SEGS B ly5 S5 W5 (ms_mem ms8) (F + 32) (Z.of_nat (length (dec max)) + 1)).
{ split; [|split; [| exact HRAd]].
  - exists 0, fpos. split; [exact Hfin5|]. split; [lia|]. rewrite Efa5. fold F. change (fs_frame_bytes 0) with 64.
    split; [|lia]. replace F with ((F / 64 * 8) * 8) at 1 by lia. apply Z_mod_mult.
  - replace (F + 32) with ((F / 64 * 8 + 4) * 8) by lia. apply Z_mod_mult. }
assert (Htlb : atail_vis SEGS W5 (ms_mem ms8) (F + 32 + Z.of_nat (length (dec max)))).
{ intros a Ha. apply crf_present_view. apply (spcb_frame_pres ly5 S5 W5 (ms_mem ms8) _ 0 fpos a HAR8 Hfin5).
  left. rewrite Efa5. fold F. change (fs_frame_bytes 0) with 64.
  pose proof (Z.mod_pos_bound (F + 32 + Z.of_nat (length (dec max))) 8 ltac:(lia)). lia. }
(* the chain and the call of arg_s(slot, b) (0x8c008) *)
spcb_chunk HS 4%nat (-8) CD8. spcb_chunk HS 4%nat (-16) CD16.
assert (Hw8d : rdword (rdW W5 (ms_mem ms8)) (spZ regs - 8) = Some (raZ regs)).
{ apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (bv_unsigned (ew E7 2) + -8) by lia.
  apply CD8; [|unfold raZ; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE7 1%nat 1%bv ltac:(lia) eq_refl). unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hw16d : rdword (rdW W5 (ms_mem ms8)) (spZ regs - 16) = Some (s0Z regs)).
{ apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (bv_unsigned (ew E7 2) + -16) by lia.
  apply CD16; [|unfold s0Z; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE7 8%nat 8%bv ltac:(lia) eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
destruct (spcb_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs + (sp1 - spZ regs)) HJ7
  (fun a Ha => proj2 (HFPlow a Ha)) Hch Hw8d Hw16d Hra4 ltac:(lia)) as (ch3 & HCH3).
assert (HFPA2 : forall a, inFP (if Z.of_nat (length [sarg (Some x)]) <? REC_ARGS_MAX
    then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
          (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg (Some x)]),
           rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg (Some x)]) + 8)]
    else []) a -> a < alloc_ceiling /\ ~ spcb_zf F a /\ rec_slot R <= a < rec_slot R + CALL_SIZE).
{ intros a Ha. unfold REC_ARGS_MAX in Ha. cbn [length Z.of_nat Z.ltb Z.compare] in Ha.
  assert (Hsl : rec_slot R <= a < rec_slot R + CALL_SIZE).
  { apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS, CALL_SIZE in *; lia | exfalso; exact (inFP_nil a Ha)]. }
  destruct (spcb_fp_apart ly S2 W mem2 md2 fpos a HAR2 Hfin2) as [Hlo Hzf].
  { destruct (spr_slot_bounds R HC1) as [Hs | Hs]; [left; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
    right; left. rewrite Hs in Hsl. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
  split; [exact Hlo|]. split; [exact Hzf | exact Hsl]. }
rewrite spcb_sig_arg_s.
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) B LAWS W5 (ms_regs ms8) (ms_mem ms8) _ SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly5 S5 _ _ ARG_S_STK _ EV_ARG_S (sp1 - spZ regs) (getr (ms_regs ms8) 1) ch3 _ HJ7 GD2
    ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
    ltac:(rewrite HAS; lia) ltac:(rewrite HAS, FS; lia) GD3 GD4 eq_refl GD1r GD1a ltac:(rewrite GD8; exact HCH3)).
  - intros HPRE1. pose proof (TARG_S fx1 ly5 S5 W5 (ms_regs ms8) (ms_mem ms8) _ ch3 (rec_slot R) (F + 32) REC_POOL_CONFIG
      [sarg (Some x)] (Some (dec max)) R ((p1, Z.of_nat (length (sarg (Some x))) + 1) :: O1) HPRE1) as T.
    cbv zeta in T. unfold apost_base in T. apply T.
    + exact HROD8.
    + exact HROk8.
    + exact GD10.
    + exact GD11.
    + reflexivity.
    + exact HREPD.
    + right. exists (dec max). split; [reflexivity|]. split; [exact Hstrb|]. split; [unfold LMAX; lia | exact Hafobj].
    + intros x0 Hx0. injection Hx0 as <-. exact Htlb.
    + pose proof HJ7 as (_ & _ & _ & _ & _ & _ & Hnv & _).
      unfold EV_SUP_POOL_CONFIG, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + rewrite Hbb2 in HBB1. pose proof (LA0 (Some x)). pose proof (LN0 (snd (sup_pool_config_m R (Some x) max))).
      unfold LIVE_SUP_POOL_CONFIG in HLIVE. lia.
    + apply (mok_station MT S2 S5 (XM_SUP_POOL_CONFIG MT R (Some x) max) (XM_RECORD MT R + XM_ARG_S MT (Some x)) _ MTL HMOK2
        (mle_station MT S2 S4 S5 _ _ MTL MLE1 MLE5) (XA0 _)).
      unfold XM_SUP_POOL_CONFIG. pose proof (XN0 (snd (sup_pool_config_m R (Some x) max))). lia.
  - intros a Ha. destruct (HFPA2 a Ha) as (_ & _ & Hsl). exact (spr_awr_slot _ _ _ _ _ _ _ _ R a HC1 Hsl).
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. destruct (HFPA2 a Ha) as [Hlo _]. lia. }
cbv beta. intros W9 c9 Hwle9 (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HJc9 & HP9 & HKb).
destruct HKb as (HBB9 & MLE9 & [(Hc7 & _) | (_ & p2 & Hp2 & Hperm9 & Hfresh9 & HREP9)]).
{ exfalso. unfold REC_ARGS_MAX in Hc7. cbn [length Z.of_nat] in Hc7. lia. }
cbn [app] in HREP9.
pose proof (proj1 HJ9) as HAR9.
pose proof HJ9 as (_ & Hly9 & _ & _ & _ & Hfrs9 & Hnev9 & _).
assert (Hfin9 : In (0, fpos) (frames S9)) by (rewrite Hfrs9; left; reflexivity).
destruct (al_layout _ _ LAWS ly S W mem md ly9 HAR Hly9) as (_ & Efa9 & _).
rewrite PD1.
jafter_call_keep_pi HS 120%nat regs9 (mrestrict (w_H W9) mem9) HP9 [0; 1; 2; 3; 4]%nat HS9.
match type of HS9 with ?tq -> _ => assert (HRK : tq); [|specialize (HS9 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc9 | exact Z57 | exact Hfin5 | unfold shadow_addr; rewrite ?Efa5; rewrite <- SB_SHADOW_OFF; fold F; lia
    | unfold shadow_addr; rewrite ?Efa5; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HFPA2 a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly9 S9 W9 mem9 md9 0 fpos a HAR9 Hfin9); right; rewrite Efa9;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc9 | exact Z44 | exact Hfin5 | rewrite ?Efa5; fold F; lia | rewrite ?Efa5; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPA2 a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc9 | exact Z44 | exact Hfin5 | rewrite ?Efa5; fold F; lia | rewrite ?Efa5; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPA2 a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly9 S9 W9 mem9 md9 0 fpos a HAR9 Hfin9); left; rewrite Efa9;
      change (fs_frame_bytes 0) with 64; fold F; lia ].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc9 | exact HJ9 | exact Z34 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPA2 a HFa) as [Hlo _]. cbn in Ha. lia.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc9 | exact HJ9 | exact Z2 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPA2 a HFa) as [Hlo _]. cbn in Ha. lia. }
rewrite <- restrict_mkst_fx in HS9. clear HS. rename HS9 into HS.
remember (havoc E7 120 (map (getr regs9) CLOB)) as E9 eqn:HE9 in HS.
assert (HEI9 : img_env VAL A_LIM E9) by (rewrite HE9; apply img_env_havoc; [exact HEI7 | cbv; lia]).
assert (OLD9 : forall n, (n < 120)%nat -> ew E9 n = ew E7 n) by (intros n Hn; rewrite HE9; apply ew_havoc_old; exact Hn).
assert (HAE9 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E9)
  by (rewrite HE9; apply env_agree_havoc_ge; [cbv; lia | exact HAE7]).
clear HE9.
assert (Va2 : bv_unsigned (ew E9 2) = spZ regs) by (rewrite OLD9 by lia; exact Z2).
assert (Va34 : bv_unsigned (ew E9 34) = sp1) by (rewrite OLD9 by lia; exact Z34).
assert (Va44 : bv_unsigned (ew E9 44) = F) by (rewrite OLD9 by lia; exact Z44).
assert (Va57 : bv_unsigned (ew E9 57) = SB + F / 8) by (rewrite OLD9 by lia; exact Z57).
assert (EE9 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E9 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD9 by lia; exact (EE7 n r Hn Hr)).
assert (Va64 : ew E9 64 = w64 (rec_slot R)) by (rewrite OLD9 by lia; exact Z64).
(* ---- run 7: 0x8c00c .. 0x8c020: b's shadow := f8 f8, a0 := "pool_config", a1 := 11, the call of rec_shape_of ---- *)
paj_run_shc RUNP1 RUNC1 HS HJ9.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact Va57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa9; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact Va44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite Efa9; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Va34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Va2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms10, mat into mat10, HF into HFq10, HFr into HFr10, HG into HG10.
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PE1. prreg HS (2%bv : bv 5) PE2. prreg HS (3%bv : bv 5) PE3. prreg HS (4%bv : bv 5) PE4.
prreg HS (10%bv : bv 5) PE10. prreg HS (11%bv : bv 5) PE11.
assert (GE2 : spZ (ms_regs ms10) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PE2, Va34; lia).
assert (GE3 : getr (ms_regs ms10) 3 = w64 (as_gp B)) by (rewrite PE3, (EE9 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GE4 : getr (ms_regs ms10) 4 = w64 (as_tp B)) by (rewrite PE4, (EE9 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (VV : VAL (A_OBJ 74) = 0x21ec0) by (rewrite (VOBJS 74%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (GE10 : getr (ms_regs ms10) 10 = w64 0x21ec0).
{ rewrite PE10. change 315%nat with (A_OBJ 74).
  rewrite (img_env_atomP E9 (A_OBJ 74) HEI9 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), VV. reflexivity. }
assert (GE11 : getr (ms_regs ms10) 11 = w64 (Z.of_nat (length spcb_verb))) by (rewrite PE11; reflexivity).
assert (GE1r : YK0s.ret_ok (getr (ms_regs ms10) 1)) by (rewrite PE1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GE1a : 4096 <= bv_unsigned (getr (ms_regs ms10) 1))
  by (rewrite PE1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
pose proof (proj1 HJ9) as HAR10.
assert (HROD10 : arodata_okP SEGS RLO RHI B (rdW W9 (ms_mem ms10)))
  by exact (spr_aro ly S W mem md O ly9 S9 W9 (ms_mem ms10) _ [(0, fpos)] _ (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ9 HROD).
assert (HROk10 : cmd_ro_ok (rdW W9 (ms_mem ms10))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR10 HROD10).
(* ---- the rec_shape_of("pool_config", 11) call (0x8c020, at fx1) ---- *)
rewrite spcb_sig_rso.
eapply SRr_bind.
{ eapply (cl_callS_na (fx := fx1) B LAWS W9 (ms_regs ms10) (ms_mem ms10) _ SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly9 S9 _ _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (sp1 - spZ regs) (getr (ms_regs ms10) 1) _ HJ9 GE2
    ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia) ltac:(rewrite HSS; lia) ltac:(rewrite HSS, FS; lia)
    GE3 GE4 eq_refl GE1r GE1a).
  - intros HPRE1. pose proof (TREC_SHAPE_OF fx1 ly9 S9 W9 (ms_regs ms10) (ms_mem ms10) _ 0x21ec0 spcb_verb HPRE1 HROD10 GE10
      ltac:(lia) GE11 ltac:(rewrite spcb_verb_len; lia) HROk10 VOBJS
      (fun _ => conj (spcb_verb_bytes _ HROk10)
        (or_intror (spcb_verb_argA SEGS B HB CMD_RLO CMD_RHI ly9 S9 _ [] HROk10 CMD_RO_IN)))) as T.
    unfold apost_base in T. apply T.
    pose proof HJ9 as (_ & _ & _ & _ & _ & _ & Hnv & _).
    unfold EV_SUP_POOL_CONFIG, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W11 c11 Hwle11 (ly11 & S11 & regs11 & mem11 & md11 & -> & HJ11 & HJc11 & HP11 & HKc).
destruct HKc as ((q & Hq10 & Hq64 & HqA) & Hperm11 & Ely11 & ES11). subst ly11 S11.
pose proof (proj1 HJ11) as HAR11.
assert (HFPN : forall a, inFP [] a -> a < alloc_ceiling /\ ~ spcb_zf F a /\ True)
  by (intros a Ha; exfalso; exact (inFP_nil a Ha)).
rewrite PE1.
jafter_call_keep_pi HS 140%nat regs11 (mrestrict (w_H W11) mem11) HP11 [0; 1; 2; 3; 4]%nat HS11.
match type of HS11 with ?tq -> _ => assert (HRK : tq); [|specialize (HS11 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc11 | exact Va57 | exact Hfin9 | unfold shadow_addr; rewrite ?Efa9; rewrite <- SB_SHADOW_OFF; fold F; lia
    | unfold shadow_addr; rewrite ?Efa9; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HFPN a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly9 S9 W11 mem11 md11 0 fpos a HAR11 Hfin9); right; rewrite Efa9;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc11 | exact Va44 | exact Hfin9 | rewrite ?Efa9; fold F; lia | rewrite ?Efa9; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPN a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc11 | exact Va44 | exact Hfin9 | rewrite ?Efa9; fold F; lia | rewrite ?Efa9; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPN a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly9 S9 W11 mem11 md11 0 fpos a HAR11 Hfin9); left; rewrite Efa9;
      change (fs_frame_bytes 0) with 64; fold F; lia ].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc11 | exact HJ11 | exact Va34 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPN a HFa) as [Hlo _]. cbn in Ha. lia.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc11 | exact HJ11 | exact Va2 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPN a HFa) as [Hlo _]. cbn in Ha. lia. }
rewrite <- restrict_mkst_fx in HS11. clear HS. rename HS11 into HS.
remember (havoc E9 140 (map (getr regs11) CLOB)) as E11 eqn:HE11 in HS.
assert (HEI11 : img_env VAL A_LIM E11) by (rewrite HE11; apply img_env_havoc; [exact HEI9 | cbv; lia]).
assert (OLD11 : forall n, (n < 140)%nat -> ew E11 n = ew E9 n) by (intros n Hn; rewrite HE11; apply ew_havoc_old; exact Hn).
assert (A144 : ew E11 144 = getr regs11 10).
{ rewrite HE11. change 144%nat with (140 + 4)%nat. rewrite (ew_havoc_new E9 140 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
assert (HAE11 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E11)
  by (rewrite HE11; apply env_agree_havoc_ge; [cbv; lia | exact HAE9]).
clear HE11.
assert (Ub2 : bv_unsigned (ew E11 2) = spZ regs) by (rewrite OLD11 by lia; exact Va2).
assert (Ub34 : bv_unsigned (ew E11 34) = sp1) by (rewrite OLD11 by lia; exact Va34).
assert (Ub44 : bv_unsigned (ew E11 44) = F) by (rewrite OLD11 by lia; exact Va44).
assert (Ub57 : bv_unsigned (ew E11 57) = SB + F / 8) by (rewrite OLD11 by lia; exact Va57).
assert (EE11 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E11 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD11 by lia; exact (EE9 n r Hn Hr)).
(* ---- run 8: 0x8c024 .. 0x8c030: a1 := the shape, a2 := 1, a0 := the slot, the call of answer ---- *)
paj_run_shc RUNP1 RUNC1 HS HJ11.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 57%nat); [reflexivity | exact Ub57 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa9; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 44%nat); [reflexivity | exact Ub44 |
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; rewrite Efa9; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Ub34; lia | cbn; rewrite FS; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Ub2; lia | cbn; rewrite FS; lia | cbn; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into ms12, mat into mat12, HF into HFq12, HFr into HFr12, HG into HG12.
pmkst HS. spcb_md.
prreg HS (1%bv : bv 5) PF1. prreg HS (2%bv : bv 5) PF2. prreg HS (3%bv : bv 5) PF3. prreg HS (4%bv : bv 5) PF4.
prreg HS (8%bv : bv 5) PF8. prreg HS (10%bv : bv 5) PF10. prreg HS (11%bv : bv 5) PF11. prreg HS (12%bv : bv 5) PF12.
assert (GF2 : spZ (ms_regs ms12) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite PF2, Ub34; lia).
assert (GF3 : getr (ms_regs ms12) 3 = w64 (as_gp B)) by (rewrite PF3, (EE11 3%nat 3%bv ltac:(lia) eq_refl); exact Hgp).
assert (GF4 : getr (ms_regs ms12) 4 = w64 (as_tp B)) by (rewrite PF4, (EE11 4%nat 4%bv ltac:(lia) eq_refl); exact Htp).
assert (GF8 : s0Z (ms_regs ms12) = spZ regs) by (unfold s0Z; rewrite PF8; exact Ub2).
assert (GF10 : getr (ms_regs ms12) 10 = w64 (rec_slot R)) by (rewrite PF10, OLD11 by lia; exact Va64).
assert (GF11 : getr (ms_regs ms12) 11 = w64 q) by (rewrite PF11, A144; exact Hq10).
assert (GF12 : bv_unsigned (getr (ms_regs ms12) 12) = 1) by (rewrite PF12; reflexivity).
assert (GF1r : YK0s.ret_ok (getr (ms_regs ms12) 1)) by (rewrite PF1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (GF1a : 4096 <= bv_unsigned (getr (ms_regs ms12) 1))
  by (rewrite PF1; pose proof HBASE as (HB0 & HB1 & _); rewrite unsigned_lit_small; lia).
(* what runs 7, 8 and rec_shape_of kept: the recorder's bytes *)
assert (KE : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 24) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
  rdW W9 (ms_mem ms10) a = rdW W9 mem9 a).
{ intros a Ha H1 H2. apply (kept_of_frame (segs := SEGS) E9 _ (w_H W9) mem9 (ms_mem ms10)
    (fun a => alloc_ceiling <= a \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 8) HFr10); [| lia | lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Va57, ?Va44, ?Va34, ?Va2 in Hrr; lia|]).
  destruct Hin. }
assert (KF : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 24) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
  rdW W11 (ms_mem ms12) a = rdW W11 mem11 a).
{ intros a Ha H1 H2. apply (kept_of_frame (segs := SEGS) E11 _ (w_H W11) mem11 (ms_mem ms12)
    (fun a => alloc_ceiling <= a \/ F <= a < F + 24 \/ SB + F / 8 <= a < SB + F / 8 + 8) HFr12); [| lia | lia].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Ub57, ?Ub44, ?Ub34, ?Ub2 in Hrr; lia|]).
  destruct Hin. }
pose proof (proj1 HJ11) as HAR12.
set (OA := (p2, Z.of_nat (length (sarg (Some (dec max)))) + 1) :: (p1, Z.of_nat (length (sarg (Some x))) + 1) :: O1) in *.
set (RA := rec_record R REC_POOL_CONFIG [sarg (Some x); sarg (Some (dec max))]) in *.
assert (HOAin : forall qn, In qn OA -> In qn (ablocks B ly9 S9)) by exact (spr_O_in ly9 S9 _ _ OA HREP9).
assert (HFP9 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  exists b m, In (b, m) (ablocks B ly9 S9) /\ b <= a < b + req_size m) -> 0 <= a < alloc_ceiling /\ ~ spcb_zf F a).
{ intros a Ha. pose proof (spcb_fp_apart ly9 S9 W9 mem9 md9 fpos a HAR9 Hfin9 Ha) as Hq. rewrite Efa9 in Hq.
  destruct Hq as [Hq1 Hq2]. split; [|exact Hq2].
  destruct Ha as [Hq | [Hq | (b & m & Hbm & Hba)]]; [unfold A_G_REC in Hq; lia | unfold A_REC_SPILL in Hq; lia|].
  destruct (spr_blk_bounds ly9 S9 W9 mem9 md9 b m HAR9 Hbm). lia. }
assert (K129 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  exists b m, In (b, m) (ablocks B ly9 S9) /\ b <= a < b + req_size m) -> rdW W11 (ms_mem ms12) a = rdW W9 mem9 a).
{ intros a Ha. destruct (HFP9 a Ha) as [Hlo Hzf]. unfold spcb_zf in Hzf.
  rewrite (KF a Hlo ltac:(lia) ltac:(lia)).
  destruct Ha as [Ha | [Ha | (b & m & Hbm & Hba)]].
  - rewrite (spr_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc11 (Forall_nil _) (inFP_nil a) (spr_grec_in a Ha)).
    exact (KE a Hlo ltac:(lia) ltac:(lia)).
  - rewrite (spr_keep_prog _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc11 (Forall_nil _) (inFP_nil a) (spr_spill_in a Ha)).
    exact (KE a Hlo ltac:(lia) ltac:(lia)).
  - replace a with (b + (a - b)) by lia.
    assert (Hbm11 : In (b, m) (ablocks B ly9 S9)) by exact Hbm.
    rewrite (spr_keep_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc11 Hbm
      ltac:(apply (Permutation_in _ (Permutation_sym Hperm11)); exact Hbm) ltac:(lia) (inFP_nil _)).
    replace (b + (a - b)) with a by lia. exact (KE a Hlo ltac:(lia) ltac:(lia)). }
assert (HREPE : rec_repA B ly9 S9 (rdW W11 (ms_mem ms12)) RA OA).
{ apply (spr_rec_repA_ext ly9 S9 (rdW W9 mem9) ly9 S9 _ _ _ HREP9 HOAin).
  intros a Ha. apply K129. destruct Ha as [Ha | [Ha | ([b m] & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha|].
  right; right. exists b, m. split; [exact (HOAin _ Hq)|]. cbn [fst snd] in Ha.
  destruct (spr_blk_bounds ly9 S9 W9 mem9 md9 b m HAR9 (HOAin _ Hq)) as (_ & _ & _ & Hm & _). lia. }
assert (HROD12 : arodata_okP SEGS RLO RHI B (rdW W11 (ms_mem ms12)))
  by exact (spr_aro ly S W mem md O ly9 S9 W11 (ms_mem ms12) _ [(0, fpos)] _ (spZ regs) SUP_POOL_CONFIG_STK HAR HOin HJ11 HROD).
assert (HROk12 : cmd_ro_ok (rdW W11 (ms_mem ms12))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HAR12 HROD12).
pose proof HREPE as (QD & HQD & HOQD).
destruct (spr_old_at _ _ _ _ HQD) as [HOLD HOLDin'].
set (old := spr_old QD) in *.
assert (Hold64 : 0 <= old < 2 ^ 64).
{ unfold old, spr_old. destruct (l_answer QD) as [an|] eqn:Ean; [|lia].
  pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han. destruct an as [a1 a2].
  destruct (spr_blk_bounds ly9 S9 W9 mem9 md9 a1 a2 HAR9 (HOAin _ Han)) as (Hb0 & Hb1 & _ & _ & Hr1). cbn [fst]. lia. }
(* the shape string at the call: rec_shape_of's (any O) kept over run 8 *)
assert (HqA12 : astr_argA B ly9 S9 (rdW W11 (ms_mem ms12)) (in_roP SEGS RLO RHI) OA q (Some (shape_of spcb_verb))).
{ apply (spr_argA_kept _ _ (rdW W11 mem11)); [exact (HqA OA)|]. intros i Hi.
  destruct (spcb_argA_nzf ly9 S9 W11 mem11 md11 fpos OA q (shape_of spcb_verb) i HAR11 Hfin9 (HqA OA) Hi) as [Hlo Hzf].
  rewrite Efa9 in Hzf. fold F in Hzf. unfold spcb_zf in Hzf. exact (KF (q + i) Hlo ltac:(lia) ltac:(lia)). }
(* the blocks of the recorder at the call that were live at the entry are the entry's recorder blocks *)
assert (HOAS : forall qn, In qn OA -> In qn (ablocks B ly S) -> In qn O).
{ intros qn Hq HS0. rewrite <- Eab in HS0. apply (Permutation_in _ HPermF) in HS0. apply in_app_or in HS0 as [H4 | HFr0];
  [|exact (HFO _ HFr0)].
  destruct Hq as [<- | [<- | Hq]].
  - exfalso. rewrite Forall_forall in Hfresh9.
    pose proof (Hfresh9 _ (Permutation_in _ (Permutation_sym Hperm5) (or_intror H4))) as D.
    unfold iv_apart in D. cbn [fst snd] in D. lia.
  - exfalso. rewrite Forall_forall in Hfresh5. pose proof (Hfresh5 _ H4) as D. unfold iv_apart in D. cbn [fst snd] in D. lia.
  - exact (proj1 (proj1 (HO1 qn) Hq)). }
(* the chain and the call of answer(slot, shape, 1) (0x8c030, at fx1; its post is FP-existential) *)
spcb_chunk HS 4%nat (-8) CF8. spcb_chunk HS 4%nat (-16) CF16.
assert (Hw8f : rdword (rdW W11 (ms_mem ms12)) (spZ regs - 8) = Some (raZ regs)).
{ apply rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  replace (spZ regs - 8) with (bv_unsigned (ew E11 2) + -8) by lia.
  apply CF8; [|unfold raZ; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE11 1%nat 1%bv ltac:(lia) eq_refl). unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hw16f : rdword (rdW W11 (ms_mem ms12)) (spZ regs - 16) = Some (s0Z regs)).
{ apply rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  replace (spZ regs - 16) with (bv_unsigned (ew E11 2) + -16) by lia.
  apply CF16; [|unfold s0Z; split; [apply bv_unsigned_in_range|]; apply bv_unsigned_in_range | lia].
  rewrite spcb_off0, (EE11 8%nat 8%bv ltac:(lia) eq_refl). unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
destruct (spcb_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs + (sp1 - spZ regs)) HJ11
  (fun a Ha => proj2 (HFPlow a Ha)) Hch Hw8f Hw16f Hra4 ltac:(lia)) as (ch4 & HCH4).
assert (HM : sup_pool_config_m R (Some x) max = rec_answer RA (REC_POOL_CONFIG, [sarg (Some x); sarg (Some (dec max))])
  (shape_of spcb_verb) true) by exact (spcb_model R (Some x) max).
set (tA := snd (rec_answer RA (REC_POOL_CONFIG, [sarg (Some x); sarg (Some (dec max))]) (shape_of spcb_verb) true)) in *.
assert (HFPAn : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) :: (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
    ablocks_fp (filter (fun pn => fst pn =? old) OA)) a -> a < alloc_ceiling /\ ~ spcb_zf F a /\ True).
{ intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    exists b m, In (b, m) (ablocks B ly9 S9) /\ b <= a < b + req_size m).
  { apply inFP_cons in Ha as [Ha | Ha]; [left; unfold A_G_REC, OFF_ANSWER, REC_SIZE in *; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [left; unfold A_G_REC, OFF_STATE, REC_SIZE in *; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba). apply spr_in_filter in Hbm as [Hbm _].
    right; right. exists b, m. split; [exact (HOAin _ Hbm) | exact Hba]. }
  destruct (HFP9 a Ha') as [Hlo Hzf]. split; [lia|]. split; [exact Hzf | exact I]. }
rewrite spcb_sig_answer.
eapply (srr_after_callF (fx := fx1) SEGS).
{ eapply (cl_callS_wideF (fx := fx1) B LAWS W11 (ms_regs ms12) (ms_mem ms12) _ SUP_POOL_CONFIG_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly9 S9 _ _ ANSWER_STK _ EV_ANSWER (sp1 - spZ regs) (getr (ms_regs ms12) 1) ch4 _ HJ11 GF2
    ltac:(rewrite Zminus_mod, Hsp1al16, Hal16; reflexivity) ltac:(lia)
    ltac:(rewrite HNS; lia) ltac:(rewrite HNS, FS; lia) GF3 GF4 eq_refl GF1r GF1a ltac:(rewrite GF8; exact HCH4)).
  - intros HPRE1. pose proof (TANSWER fx1 ly9 S9 W11 (ms_regs ms12) (ms_mem ms12) _ ch4 (rec_slot R) q old
      (REC_POOL_CONFIG, [sarg (Some x); sarg (Some (dec max))]) (shape_of spcb_verb) true RA OA HPRE1) as T.
    cbv zeta in T. apply T.
    + exact (fxrel_frm0 fx fx1 HFRM Hfx).
    + rewrite Hfrs9. cbn [length app]. lia.
    + exact HROD12.
    + exact HROk12.
    + exact GF10.
    + destruct (spr_slot_bounds R HC1) as [Hs | Hs]; [unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia|].
      rewrite Hs. unfold A_REC_SPILL. lia.
    + exact GF11.
    + exact Hq64.
    + rewrite GF12. reflexivity.
    + exact HREPE.
    + exact HOLD.
    + exact Hold64.
    + intros _. split; [exact HqA12 | exact spcb_fits].
    + intros _ _. exact (spr_answer_slot R REC_POOL_CONFIG [sarg (Some x); sarg (Some (dec max))]).
    + pose proof HJ11 as (_ & _ & _ & _ & _ & _ & Hnv & _).
      unfold EV_SUP_POOL_CONFIG, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
    + unfold LIVE_SUP_POOL_CONFIG in HLIVE. rewrite HM in HLIVE. fold tA in HLIVE |- *. rewrite Hbb2 in HBB1. lia.
    + fold tA. apply (mok_station MT S2 S9 (XM_SUP_POOL_CONFIG MT R (Some x) max)
        (XM_RECORD MT R + XM_ARG_S MT (Some x) + XM_ARG_S MT (Some (dec max))) _ MTL HMOK2
        (mle_station MT S2 S5 S9 _ _ MTL (mle_station MT S2 S4 S5 _ _ MTL MLE1 MLE5) MLE9) (XN0 _)).
      unfold XM_SUP_POOL_CONFIG. rewrite HM. fold tA. lia.
  - intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [apply spr_awr_grec; unfold OFF_ANSWER, REC_SIZE in *; lia|].
    apply inFP_cons in Ha as [Ha | Ha]; [apply spr_awr_grec; unfold OFF_STATE, REC_SIZE in *; lia|].
    destruct (inFP_ablocks_fp_inv _ a Ha) as (b & m & Hbm & Hba).
    apply spr_in_filter in Hbm as [Hbm _].
    destruct (in_dec spr_pair_dec (b, m) O) as [HbO | HbnO].
    + exact (spr_awr_blk _ _ _ _ _ _ _ _ b m a HbO (HOAin _ Hbm) Hba).
    + right; right; left. exists b, m. split; [exact (HOAin _ Hbm)|].
      split; [intros HbS; exact (HbnO (HOAS _ Hbm HbS)) | exact Hba].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. destruct (HFPAn a Ha) as [Hlo _]. lia. }
intros fx2 ly13 S13 W13 regs13 mem13 md13 Hle13 Hfx2 (HJ13 & HJc13 & HP13 & HKd).
destruct HKd as (q1 & q2 & O' & G10 & G4096 & Gne & Gfr & GBL & GREP & GO & GSTR & GBB & GMLE).
fold tA in GBB. fold tA in GMLE.
(* ---- after answer, at its FP state fx2: the frame's release and the epilogue ---- *)
pose proof (proj1 HJ13) as HAR13.
pose proof HJ13 as (_ & Hly13 & _ & _ & _ & Hfrs13 & Hnev13 & _).
assert (Hfin13 : In (0, fpos) (frames S13)) by (rewrite Hfrs13; left; reflexivity).
destruct (al_layout _ _ LAWS ly S W mem md ly13 HAR Hly13) as (_ & Efa13 & _).
pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl) as Ems12. rewrite Ems12 in HS. clear Ems12.
lazymatch type of HS with @st_ok ?sg _ ?Ex ?ssx (restrict ?Hx (@mkst _ ?r ?p ?m ?ro)) =>
  pose proof (st_ok_restrict_xfx fx1 fx2 sg Ex ssx Hx _ HS ltac:(vm_compute; reflexivity)
    : @st_ok sg fx2 Ex ssx (restrict Hx (@mkst fx2 r p m ro))) as HSf end. clear HS. rename HSf into HS.
rewrite PF1.
jafter_call_keep_pi HS 160%nat regs13 (mrestrict (w_H W13) mem13) HP13 [0; 1; 2; 3; 4]%nat HS13.
match type of HS13 with ?tq -> _ => assert (HRK : tq); [|specialize (HS13 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_fshadow_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc13 | exact Ub57 | exact Hfin9 | unfold shadow_addr; rewrite ?Efa9; rewrite <- SB_SHADOW_OFF; fold F; lia
    | unfold shadow_addr; rewrite ?Efa9; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia
    | intros a Ha HFa; destruct (HFPAn a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly13 S13 W13 mem13 md13 0 fpos a HAR13 Hfin13); right; rewrite Efa13;
      unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 0 / 8) with 8; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc13 | exact Ub44 | exact Hfin9 | rewrite ?Efa9; fold F; lia | rewrite ?Efa9; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPAn a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; lia ].
  - eapply (region_kept_frame_sub B) with (cid := 0) (pos := fpos);
    [ exact HJc13 | exact Ub44 | exact Hfin9 | rewrite ?Efa9; fold F; lia | rewrite ?Efa9; change (fs_frame_bytes 0) with 64; fold F; lia
    | intros a Ha HFa; destruct (HFPAn a HFa) as [_ [Hzf _]]; apply Hzf; unfold spcb_zf; lia
    | intros a Ha; apply (spcb_frame_pres ly13 S13 W13 mem13 md13 0 fpos a HAR13 Hfin13); left; rewrite Efa13;
      change (fs_frame_bytes 0) with 64; fold F; lia ].
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc13 | exact HJ13 | exact Ub34 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPAn a HFa) as [Hlo _]. cbn in Ha. lia.
  - eapply (region_kept_stack_sub SEGS B);
    [exact HJc13 | exact HJ13 | exact Ub2 | cbn; lia | rewrite FS; cbn; lia | cbn; lia | cbn; lia | cbn; lia |].
    intros a Ha HFa. destruct (HFPAn a HFa) as [Hlo _]. cbn in Ha. lia. }
rewrite <- restrict_mkst_fx in HS13. clear HS. rename HS13 into HS.
remember (havoc E11 160 (map (getr regs13) CLOB)) as E13 eqn:HE13 in HS.
assert (HEI13 : img_env VAL A_LIM E13) by (rewrite HE13; apply img_env_havoc; [exact HEI11 | cbv; lia]).
assert (OLD13 : forall n, (n < 160)%nat -> ew E13 n = ew E11 n) by (intros n Hn; rewrite HE13; apply ew_havoc_old; exact Hn).
assert (A164 : ew E13 164 = getr regs13 10).
{ rewrite HE13. change 164%nat with (160 + 4)%nat. rewrite (ew_havoc_new E11 160 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
assert (HAE13 : env_agree 32 (Ereg regs (spcb_extra0 (as_uar_cell B))) E13)
  by (rewrite HE13; apply env_agree_havoc_ge; [cbv; lia | exact HAE11]).
clear HE13.
assert (Tf2 : bv_unsigned (ew E13 2) = spZ regs) by (rewrite OLD13 by lia; exact Ub2).
assert (Tf34 : bv_unsigned (ew E13 34) = sp1) by (rewrite OLD13 by lia; exact Ub34).
assert (Tf44 : bv_unsigned (ew E13 44) = F) by (rewrite OLD13 by lia; exact Ub44).
assert (Tf57 : bv_unsigned (ew E13 57) = SB + F / 8) by (rewrite OLD13 by lia; exact Ub57).
assert (Tf56 : bv_unsigned (ew E13 56) = FL)
  by (rewrite OLD13, OLD11, OLD9, OLD7, OLD5, OLD4 by lia; exact W56).
assert (EE13 : forall n (r : bv 5), (n < 34)%nat -> Z.of_nat n = bv_unsigned r -> ew E13 n = getr regs r)
  by (intros n r Hn Hr; rewrite OLD13 by lia; exact (EE11 n r Hn Hr)).
(* the flag byte FL (the frame's flag, in the fake stack's flag array): owned by the runtime, so apart from the
   frame and its shadow, which are not *)
assert (Efl13 : flag_addr ly13 0 fpos = FL) by (pose proof (Efa13 0 fpos) as Eq; unfold frame_addr in Eq; unfold FL, flag_addr; lia).
destruct (cmd_frame_flag_law B ly13 S13 W13 mem13 md13 0 fpos HAR13 Hfin13) as (HFLp13 & HFLo13 & (_ & HFLimg13) & (_ & _ & HFLc13)).
rewrite Efl13 in HFLp13, HFLo13, HFLimg13, HFLc13.
destruct (al_frames _ _ LAWS ly13 S13 W13 mem13 md13 0 fpos HAR13 Hfin13) as (_ & _ & HFp13 & HFs13).
rewrite Efa13 in HFp13, HFs13. fold F in HFp13, HFs13. change (fs_frame_bytes 0 / 8) with 8 in HFs13.
change (fs_frame_bytes 0) with 64 in HFp13.
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hc; exact (proj2 (HFp13 FL Hc) HFLo13)).
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 8)).
{ intros Hc. pose proof (proj2 (HFs13 (FL - shadow_addr F) ltac:(unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia))) as Hn.
  replace (shadow_addr F + (FL - shadow_addr F)) with FL in Hn by lia. exact (Hn HFLo13). }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 56%nat) 0 1 0 1 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite Tf56; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp13)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
      cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite Tf56, ?Tf57, ?Tf44, ?Tf34, ?Tf2; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. spcb_norm HS.
(* ---- run 9: 0x8c034 .. 0x8c0c8: the frame's magic, its shadow := f5, the flag byte := 0 (the side-stack branch:
   s2 is the frame), the epilogue, to the ret ---- *)
pose proof (aj_flag_store_pi (fx := fx2) (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS ML AFREE_LAW (cmd_frame_flag_law B)) as RUNF2.
lazymatch type of RUNF2 with forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q,
  _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ss', ?st) =>
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ss', st)) by (vm_compute; reflexivity);
      eapply (RUNF2 Wx FUEL Ex ssx ss' st msx _ _ _ _ _ _ _ _ [] _ _ _ _ 0 fpos _ HEI13 HS Hrun I HJ13)
    end end end.
- lia.
- intros a Ha. destruct (in_wrange_windows _ _ _ Ha) as (b & wlo & whi & Hi & Hr). vm_compute in Hi.
  repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?Tf56, ?Tf57, ?Tf44, ?Tf34, ?Tf2 in Hr;
    first [ right; rewrite Efl13; lia
          | left; left; rewrite FS; lia
          | left; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
            first [ left; unfold in_zr; cbn [fst snd]; rewrite Efa13; fold F; change (fs_frame_bytes 0) with 64; lia
                  | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite Efa13; fold F; rewrite <- SB_SHADOW_OFF;
                    change (fs_frame_bytes 0 / 8) with 8; lia ] ] |]).
  destruct Hi.
- intros msr Hmsr. rewrite Efl13.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ Hmsr eq_refl) as HRr.
  pose proof (spcb_region_val SEGS _ _ _ 0 1 (SLit 0) 0 HRr ltac:(cbn [YP09.r_chunks]; left; reflexivity)
    eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv0.
  pose proof (Hv0 0%nat ltac:(lia)) as Hb. cbn [base_val YP09.r_base] in Hb. rewrite Tf56 in Hb.
  replace (FL + 0 + Z.of_nat 0) with FL in Hb by lia. exact Hb.
- intros ms14 mat14 HS14 HJ14 HF14 HFr14 HG14.
  pose proof (paj_ret_at (fx := fx2) (PL := PL_cmd) (PI := PI)) as RET2.
  eapply (RET2 W13 _ _ _ _ _ HS14 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat15.
  prreg HS14 (1%bv : bv 5) PG1. prreg HS14 (10%bv : bv 5) PG10.
  assert (Hpc : v_jalr (getr (ms_regs ms14) 1) 0 = getr regs 1).
  { rewrite PG1, (EE13 1%nat 1%bv ltac:(lia) eq_refl). pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'. exact Hra'. }
  rewrite Hpc.
  assert (Eblk : ablocks B ly13 (stack_free_state 0 fpos S13) = ablocks B ly13 S13) by reflexivity.
  assert (Ebb : blocks_bytes (stack_free_state 0 fpos S13) = blocks_bytes S13) by reflexivity.
  apply (apost_baseF_intro (fx := fx2) SEGS fx2 B SUP_POOL_CONFIG_STK FP regs ly S W mem md (EV_SUP_POOL_CONFIG R) _ W13
    ly13 (stack_free_state 0 fpos S13) (ms_regs ms14) (ms_mem ms14) _ (fxrel_refl fx2)).
  { eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ14|].
    unfold EV_SUP_POOL_CONFIG, EV_REC_SHAPE_OF, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC. lia. }
  { exact (aregs_preserved_of_st_ok SEGS (w_H W13) E13 _ ms14 regs (spcb_extra0 (as_uar_cell B)) HS14 HAE13
      ltac:(vm_compute; reflexivity)). }
  cbv beta.
  (* the release run kept every byte outside the frame, its shadow and the flag byte *)
  assert (K14 : forall a, 0 <= a < alloc_ceiling -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) -> a <> FL ->
    rdW W13 (ms_mem ms14) a = rdW W13 mem13 a).
  { intros a Ha H1 H2 H3. apply (kept_of_frame (segs := SEGS) E13 _ (w_H W13) mem13 (ms_mem ms14)
      (fun a => alloc_ceiling <= a \/ F <= a < F + 64 \/ SB + F / 8 <= a < SB + F / 8 + 8 \/ a = FL) HFr14); [| lia | lia].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Tf56, ?Tf57, ?Tf44, ?Tf34, ?Tf2 in Hrr; lia|]).
    destruct Hin. }
  assert (HnFL : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    exists b m, In (b, m) (ablocks B ly13 S13) /\ b <= a < b + req_size m) -> 0 <= a < alloc_ceiling /\ ~ spcb_zf F a /\ a <> FL).
  { intros a Ha. destruct (spcb_fp_apart ly13 S13 W13 mem13 md13 fpos a HAR13 Hfin13 Ha) as [Hlo Hzf].
    rewrite Efa13 in Hzf. fold F in Hzf.
    split; [|split; [exact Hzf|]].
    { destruct Ha as [Hq | [Hq | (b & m & Hbm & Hba)]]; [unfold A_G_REC in Hq; lia | unfold A_REC_SPILL in Hq; lia|].
      destruct (spr_blk_bounds ly13 S13 W13 mem13 md13 b m HAR13 Hbm). lia. }
    intros ->. destruct Ha as [Ha | [Ha | (b & m & Hbm & Hba)]].
    - destruct ((recb_prog_unowned_m B HB cmd_prog_img) FL (spr_grec_in FL Ha)) as (Hi & _). exact (HFLimg13 Hi).
    - destruct ((recb_prog_unowned_m B HB cmd_prog_img) FL (spr_spill_in FL Ha)) as (Hi & _). exact (HFLimg13 Hi).
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR13 Hbm) as (_ & _ & _ & _ & Hown & _). exact (proj2 (Hown FL Hba) HFLo13). }
  assert (K14r : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    exists b m, In (b, m) (ablocks B ly13 S13) /\ b <= a < b + req_size m) -> rdW W13 (ms_mem ms14) a = rdW W13 mem13 a).
  { intros a Ha. destruct (HnFL a Ha) as (Hlo & Hzf & Hfl). unfold spcb_zf in Hzf. exact (K14 a Hlo ltac:(lia) ltac:(lia) Hfl). }
  assert (H4to5 : forall qn, In qn (ablocks B ly4 S4) -> In qn (ablocks B ly5 S5))
    by (intros qn Hq; apply (Permutation_in _ (Permutation_sym Hperm5)); right; exact Hq).
  assert (H5to9 : forall qn, In qn (ablocks B ly5 S5) -> In qn (ablocks B ly9 S9))
    by (intros qn Hq; apply (Permutation_in _ (Permutation_sym Hperm9)); right; exact Hq).
  assert (HSsplit : forall qn, In qn (ablocks B ly S) -> In qn (ablocks B ly4 S4) \/ In qn Fr)
    by (intros qn Hq; rewrite <- Eab in Hq; apply in_app_or; exact (Permutation_in _ HPermF Hq)).
  assert (HFnot : forall qn, In qn Fr -> ~ In qn (ablocks B ly4 S4))
    by (intros qn HFi H4; exact (spr_dup_false ly S2 W mem2 md2 (ablocks B ly4 S4) Fr qn HAR2 HPermF H4 HFi)).
  assert (HOLDin : forall qn, In qn (ablocks B ly9 S9) -> fst qn = old -> In qn OA).
  { intros qn Hqn Hf. unfold old, spr_old in Hf. destruct (l_answer QD) as [an|] eqn:Ean.
    - pose proof (HOLDin' an eq_refl) as Han. apply HOQD in Han.
      rewrite (spr_same_start ly9 S9 W9 mem9 md9 qn an HAR9 Hqn (HOAin _ Han) Hf). exact Han.
    - destruct qn as [b m]. destruct (spr_blk_bounds ly9 S9 W9 mem9 md9 b m HAR9 Hqn) as (Hb & _). cbn [fst] in Hf. lia. }
  assert (Hnew12 : forall qn, In qn (ablocks B ly S) ->
    (qn = (q1, Z.of_nat (length tA) + 1) \/ qn = (q2, Z.of_nat (length tA) + 1)) -> In qn O).
  { intros qn HS0 Heq. destruct (HSsplit _ HS0) as [H4 | HFi]; [|exact (HFO _ HFi)].
    pose proof (H5to9 _ (H4to5 _ H4)) as H9.
    destruct (Z.eq_dec (fst qn) old) as [Ho | Ho]; [exact (HOAS _ (HOLDin _ H9 Ho) HS0)|].
    exfalso. destruct (Gfr qn H9 Ho) as [N1 N2]. destruct Heq as [Heq | Heq]; [exact (N1 Heq) | exact (N2 Heq)]. }
  exists (fst (rec_answer RA (REC_POOL_CONFIG, [sarg (Some x); sarg (Some (dec max))]) (shape_of spcb_verb) true)), tA, q2, O'.
  split; [rewrite HM; apply surjective_pairing|].
  split; [rewrite PG10, A164; exact G10|].
  split; [exact G4096|].
  split.
  { apply (spr_rec_repA_ext ly13 S13 (rdW W13 mem13) ly13 (stack_free_state 0 fpos S13) _ _ O' GREP).
    - intros qn Hq. rewrite Eblk. exact (spr_O_in ly13 S13 _ _ _ GREP qn Hq).
    - intros a Ha. apply K14r. destruct Ha as [Ha | [Ha | ([b m] & Hq & Ha)]]; [left; exact Ha | right; left; exact Ha|].
      right; right. pose proof (spr_O_in ly13 S13 _ _ _ GREP _ Hq) as Hq13. exists b, m. split; [exact Hq13|].
      cbn [fst snd] in Ha. destruct (spr_blk_bounds ly13 S13 W13 mem13 md13 b m HAR13 Hq13) as (_ & _ & _ & Hm & _). lia. }
  split.
  { intros qn Hqn. destruct (in_dec spr_pair_dec qn (ablocks B ly S)) as [HS0 | HnS]; [left | right; exact HnS].
    apply GO in Hqn as [[H3 _] | ->]; [exact (HOAS qn H3 HS0) | exact (Hnew12 _ HS0 (or_introl eq_refl))]. }
  split; [rewrite Eblk; apply GBL; right; right; reflexivity|].
  split; [intros qn HS0 HnO Heq; subst qn; exact (HnO (Hnew12 _ HS0 (or_intror eq_refl)))|].
  split.
  { intros Hin. apply in_map_iff in Hin as (qn & Hf & Hqn).
    pose proof (spr_O_in ly13 S13 _ _ _ GREP qn Hqn) as Hqn13.
    pose proof (proj2 (GBL (q2, Z.of_nat (length tA) + 1)) (or_intror (or_intror eq_refl))) as Hq13.
    pose proof (spr_same_start ly13 S13 W13 mem13 md13 qn (q2, Z.of_nat (length tA) + 1) HAR13 Hqn13 Hq13 Hf) as ->.
    apply GO in Hqn as [[Hqn1 Hfo] | Heq];
    [exact (proj2 (Gfr _ (HOAin _ Hqn1) Hfo) eq_refl) | injection Heq as Heq; exact (Gne (eq_sym Heq))]. }
  split.
  { apply (spr_str_keep (rdW W13 mem13)); [exact GSTR|]. intros a Ha.
    pose proof (proj2 (GBL (q2, Z.of_nat (length tA) + 1)) (or_intror (or_intror eq_refl))) as Hq13.
    apply K14r. right; right. exists q2, (Z.of_nat (length tA) + 1). split; [exact Hq13|].
    destruct (spr_blk_bounds ly13 S13 W13 mem13 md13 _ _ HAR13 Hq13) as (_ & _ & _ & Hm & _). lia. }
  split.
  { intros qn Hqn HnO.
    assert (H4 : In qn (ablocks B ly4 S4)) by (destruct (HSsplit _ Hqn) as [H | H]; [exact H | exfalso; exact (HnO (HFO _ H))]).
    pose proof (H5to9 _ (H4to5 _ H4)) as H9.
    assert (Ho : fst qn <> old) by (intros Hf; exact (HnO (HOAS _ (HOLDin _ H9 Hf) Hqn))).
    assert (H13 : In qn (ablocks B ly13 S13)) by (apply GBL; left; split; [exact H9 | exact Ho]).
    split; [rewrite Eblk; exact H13|].
    pose proof (proj2 (GBL (q2, Z.of_nat (length tA) + 1)) (or_intror (or_intror eq_refl))) as Hq13.
    destruct qn as [b m]. cbn [fst snd].
    assert (Hne : (b, m) <> (q2, Z.of_nat (length tA) + 1)) by exact (proj2 (Gfr (b, m) H9 Ho)).
    destruct (spr_blk_bounds ly13 S13 W13 mem13 md13 b m HAR13 H13) as (_ & _ & Hm0 & Hmr & _).
    destruct (spr_blk_bounds ly13 S13 W13 mem13 md13 _ _ HAR13 Hq13) as (_ & _ & Hn0 & Hnr & _).
    unfold iv_apart. destruct (spr_blk_apart ly13 S13 W13 mem13 md13 b m q2 _ HAR13 H13 Hq13 Hne); lia. }
  split.
  { intros qn Hqn. rewrite Eblk in Hqn. apply GBL in Hqn as [[H9 Hf] | [-> | ->]].
    - apply (Permutation_in _ Hperm9) in H9. destruct H9 as [<- | H5].
      + right; left. apply GO. left. split; [left; reflexivity | exact Hf].
      + apply (Permutation_in _ Hperm5) in H5. destruct H5 as [<- | H4].
        * right; left. apply GO. left. split; [right; left; reflexivity | exact Hf].
        * destruct (in_dec spr_pair_dec qn O1) as [H1 | H1n].
          -- right; left. apply GO. left. split; [right; right; exact H1 | exact Hf].
          -- left. split.
             ++ rewrite <- Eab. apply (Permutation_in _ (Permutation_sym HPermF)). apply in_or_app. left. exact H4.
             ++ intros HinO. apply H1n. apply HO1. split; [exact HinO | intros HFi; exact (HFnot _ HFi H4)].
    - right; left. apply GO. right. reflexivity.
    - right; right. reflexivity. }
  split.
  { rewrite Ebb. unfold LIVE_SUP_POOL_CONFIG. rewrite HM. fold tA. rewrite Hbb2 in HBB1.
    clear - GBB HBB9 HBB5 HBB1. lia. }
  assert (MLEf : mo_le MT S13 (stack_free_state 0 fpos S13) 0)
    by (exact (mo_le_set_fs_r MT MTLF _ _ _ _ (mo_le_refl MT MTL S13))).
  apply (mle_weaken MT S _ _ _ MTL (mle_station MT S S13 _ _ _ MTL
    (mle_station MT S S9 S13 _ _ MTL (mle_station MT S S2 S9 _ _ MTL MLE2
      (mle_station MT S2 S5 S9 _ _ MTL (mle_station MT S2 S4 S5 _ _ MTL MLE1 MLE5) MLE9)) GMLE) MLEf)).
  unfold XM_SUP_POOL_CONFIG. rewrite HM. fold tA. lia.
Qed.



End e.
End f.
End a.
