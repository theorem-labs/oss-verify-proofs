(* The fake-frame lemmas check_step and LLVMFuzzerTestOneInput share. Both are PROVED: `frame_setup` for every cid
   and n (a Theorem Labs lane, 2026-10-28) and `afobj_of_own`.

   The fake-frame argument that libreac/fuzz_scene's two ASan walks share: check_step (class 2, __asan_stack_malloc_2
   with a0 = 224) and LLVMFuzzerTestOneInput (class 8, __asan_stack_malloc_8 with a0 = 9408). Image-free: `segs`,
   `val` and `B` are arguments, so the asan and the asan-ubsan walks of both functions use the same file.

   - frame_setup_stmt / frame_setup: the frame-region setup after the class's stack-malloc call, parametric in the
     class `cid` and the size `n` whose shadow the call zeroed (the shadow length is n / 8; the number k of 8-byte
     zero chunks and the write window [wlo, whi) are quantified). The text of fzero_chunks, frame_ss and
     frame_setup_stmt is a Theorem Labs lane's, word for word (at f8e11ff3ccb,
     lib/A/P_LLVMFuzzerTestOneInput.v:129-156), a port of cgif_file_fuzzer A/ACk1.v:209-277 (class 1 there).
     Instances: LLVMFuzzerTestOneInput `frame_setup SEGS VAL B 8 9408` (its HFRAME8); check_step
     `frame_setup SEGS VAL B 2 (fs_frame_bytes 2)` after A/Prog/YC85.v:292 aj_stack_malloc_atS, whose post zeroes
     the shadow of the whole 256-byte class-2 frame (Reusable/YG0d.v:295).
   - afobj_of_own: a caller's journal whose `own` holds the frame of a local, the local inside that frame, 8-aligned
     and marked usable, gives the per-function frame-object premise `afobj` (A/Prog/SceneBase.v:51) at the caller's
     current state (cgif_file_fuzzer YC21.v:41, :96 take such an object). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05 YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaRun SceneBase SceneFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
(* ---- the fake-frame region setup (a Theorem Labs lane's text, P_LLVMFuzzerTestOneInput.v:129-156 at f8e11ff3ccb) ---- *)
Definition fzero_chunks (k : nat) : list YP09.chunk :=
map (fun j => YP09.mkChunk (8 * Z.of_nat j) (CVal 8 (SLit 0))) (seq 0 k).
Definition frame_ss (f fl s bx : nat) (cid : Z) (k : nat) (wlo whi : Z) (ss : sstate) : sstate :=
let ss1 := add_atom (add_atom (add_atom ss f (HPTR 5)) fl (HPTR 0)) s (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2) in
let ss2 := set_facts ss1 (mkFacts (f_atoms (ss_facts ss1)) (f_conds (ss_facts ss1))
((SAlu ALU_ADD (SAlu ALU_SRL (SOff f 0) (SLit 3)) (SOff bx 0), SOff s 0) :: f_alias (ss_facts ss1))) in
mkSS (ss_pc ss2) (ss_regs ss2)
(fshadow_region s cid wlo whi (fzero_chunks k) :: fframe_region f fl cid [] :: ss_mem ss2) (ss_resv ss2) (ss_facts ss2).
Definition frame_setup_stmt (segs : list Segment) (val : nat -> Z) (B : asyms) (cid n : Z) : Prop :=
AR_laws segs B ->
forall (W : world segs) (E : env) (ss : sstate) (ms : machine_state) (md : Model) ly S pos
(f fl s bx : nat) (k : nat) (wlo whi : Z),
st_ok_pi segs val E ss (restrict (w_H W) ms) ->
AR segs B ly S W (ms_mem ms) md -> In (cid, pos) (frames S) ->
ew E f = Z_to_bv 64 (frame_addr ly cid pos) ->
ew E fl = Z_to_bv 64 (flag_addr ly cid pos) ->
ew E bx = Z_to_bv 64 SHADOW_OFF ->
ew E s = Z_to_bv 64 (SHADOW_OFF + frame_addr ly cid pos / 8) ->
rdword (aview segs (w_H W) (ms_mem ms)) (frame_addr ly cid pos + fs_frame_bytes cid - 8) = Some (flag_addr ly cid pos) ->
8 <= n <= fs_frame_bytes cid -> n mod 8 = 0 ->
zero_shadow (aview segs (w_H W) (ms_mem ms)) SHADOW_OFF (frame_addr ly cid pos) n ->
8 * Z.of_nat k <= n / 8 ->
0 <= wlo <= whi -> whi <= fs_frame_bytes cid / 8 ->
region_wf (fframe_region f fl cid []) = true ->
region_wf (fshadow_region s cid wlo whi (fzero_chunks k)) = true ->
all_disjoint E (fframe_region f fl cid []) (ss_mem ss) ->
all_disjoint E (fshadow_region s cid wlo whi (fzero_chunks k)) (fframe_region f fl cid [] :: ss_mem ss) ->
st_ok_pi segs val E (frame_ss f fl s bx cid k wlo whi ss) (restrict (w_H W) ms).
(* Eight zero shadow bytes read through the reader view give an 8-byte zero chunk (cgif_file_fuzzer YC4b.v:88,
   image-free). *)
Lemma fs_val_mem_zero8 : forall segs H (m : word -> option byte) a,
(forall i, 0 <= i < 8 -> aview segs H m (a + i) = Some 0) -> val_mem segs (mrestrict H m) a 8 0.
Proof.
intros segs H m a Hz j Hj. destruct (aview_byte segs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
(* The setup holds at every class and size: the three atom facts from the frame law (al_frames: 32-aligned, in the
   application range; al_flag: the flag cell in the application range), the shadow alias by shadow_decl_ok, the
   frame region from the frame bytes' presence and the flag word, the shadow region from the frame shadow's presence
   and the zeroed shadow (cgif_file_fuzzer A/ACk1.v:209-277, generalised over cid / n). *)
Lemma frame_setup : forall segs val B cid n, frame_setup_stmt segs val B cid n.
Proof.
intros segs val B cid n LAWS W E ss ms md ly S pos f fl s bx k wlo whi
HS HAR Hin Ef Efl Ebx Es Hflag Hn Hn8 Hz Hk Hw Hwhi Hwf1 Hwf2 Hd1 Hd2.
destruct (al_frames _ _ LAWS ly S W (ms_mem ms) md cid pos HAR Hin) as (Hal & Happ & Hpres & Hspres).
destruct (al_flag _ _ LAWS ly S W (ms_mem ms) md cid pos HAR Hin) as (_ & _ & Hflapp & Hflc).
pose proof alloc_ceiling_val as Hac.
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
set (F := frame_addr ly cid pos) in *. set (FL := flag_addr ly cid pos) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hflapp.
assert (HF : 4096 <= F /\ F + fs_frame_bytes cid <= 140737479966720) by lia.
assert (HFL : 4096 <= FL < 140737479966720) by lia.
destruct (proj1 (Z.mod_divide F 32 ltac:(lia)) Hal) as [q Hq].
assert (HF8 : F / 8 = 4 * q) by (rewrite Hq; replace (q * 32) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
assert (Hb8 : fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
assert (UF : bv_unsigned (ew E f) = F) by (rewrite Ef; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (ew E fl) = FL) by (rewrite Efl; apply unsigned_lit_small; lia).
assert (US : bv_unsigned (ew E s) = SHADOW_OFF + F / 8) by (rewrite Es; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
unfold st_ok_pi in *.
pose proof (st_ok_add_fact segs E _ _ f (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite UF; change (2 ^ 5) with 32; lia)) as HS1.
pose proof (st_ok_add_fact segs E _ _ fl (HPTR 0) HS1
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite UFL, Z.pow_0_r, Z.mod_1_r; lia)) as HS2.
pose proof (st_ok_add_fact segs E _ _ s (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 2) HS2
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite US, HF8; change (2 ^ 2) with 4; unfold SHADOW_OFF;
split; [lia|]; split; [replace (2147450880 + 4 * q) with ((536862720 + q) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
pose proof (st_ok_add_alias segs E _ _ _ _ HS3 (shadow_decl_ok E f bx s F SHADOW_OFF Ef ltac:(lia) Ebx Es)) as HS4.
assert (R1 : region_ok segs E (ms_mem (restrict (w_H W) ms)) (fframe_region f fl cid [])).
{ unfold region_ok, fframe_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict app].
rewrite UF. split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable segs). exact (proj1 (Hpres (F + o) ltac:(lia))).
- apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ F (fs_frame_bytes cid - 8) 8 (SOff fl 0) FL).
+ cbn [sv_denot]. rewrite Efl, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
+ change (8 * Z.of_N 8) with 64. lia.
+ change (Z.of_N 8) with 8. lia.
+ replace (F + (fs_frame_bytes cid - 8)) with (F + fs_frame_bytes cid - 8) by lia.
exact (val_mem_of_rdword segs _ _ _ _ Hflag). }
pose proof (ast_ok_add_region segs E _ _ (fframe_region f fl cid []) HS4 Hwf1 R1 Hd1) as HS5.
assert (R2 : region_ok segs E (ms_mem (restrict (w_H W) ms)) (fshadow_region s cid wlo whi (fzero_chunks k))).
{ unfold region_ok, fshadow_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
rewrite US. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split.
- intros o Ho. apply (apresent_writable segs). pose proof (proj1 (Hspres o ltac:(lia))) as Hp.
unfold shadow_addr in Hp. exact Hp.
- unfold fzero_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
apply (chunk_ok_val segs E _ (SHADOW_OFF + F / 8) (8 * Z.of_nat j) 8 (SLit 0) 0).
+ reflexivity.
+ change (8 * Z.of_N 8) with 64. lia.
+ change (Z.of_N 8) with 8. lia.
+ apply fs_val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz.
replace (SHADOW_OFF + F / 8 + 8 * Z.of_nat j + i) with (SHADOW_OFF + F / 8 + (8 * Z.of_nat j + i)) by lia.
apply Hz. lia. }
pose proof (ast_ok_add_region segs E _ _ (fshadow_region s cid wlo whi (fzero_chunks k)) HS5 Hwf2 R2 Hd2) as HS6.
exact HS6.
Qed.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Let LAWS : AR_laws segs B := AR_laws_ok segs B.  (* Reusable/YG0q.v:803 *)
Lemma afobj_of_own : forall STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k cid pos p n,
ajournal segs B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
In (cid, pos) own -> 0 <= cid ->
frame_addr ly cid pos <= p -> p + n <= frame_addr ly cid pos + fs_frame_bytes cid ->
p mod 8 = 0 ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n ->
afobj segs B ly S W mem p n.
Proof.
intros STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k cid pos p n HJ Hin Hcid Hlo Hhi Hal Hra.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (HinS : In (cid, pos) (frames S)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR HinS) as (H32 & _).
split; [|split; [exact Hal | exact Hra]].
exists cid, pos. split; [exact HinS|]. split; [exact Hcid|]. split; [|split; [exact Hlo | exact Hhi]].
apply Z.mod_divide; [lia|]. apply Z.mod_divide in H32; [|lia]. destruct H32 as [q Hq]. exists (4 * q). lia.
Qed.
End e.
End d.
Print Assumptions frame_setup.
Print Assumptions afobj_of_own.
About frame_setup_stmt.
About afobj_of_own.
