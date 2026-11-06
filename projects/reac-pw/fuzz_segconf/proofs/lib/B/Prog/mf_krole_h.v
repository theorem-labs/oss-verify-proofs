(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 534 of its 589 lines of code are new or changed and 398 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KROLE, piece kr_s_hit: the
   hit path of the role key, KR_HIT 0x868c8 (lib/B/Prog/mf_krole_m.v) to KDONE 0x86c1c. A walk lane of
   the image-B m_file-family owner's G2B (a piece agent). proves no function (kind: segment lemma of m_file's image-B walk, S_MF_KROLE
   piece kr_s_hit). Adapted from image A's lib/A/Prog/m_file_s_krole_h.v (the image-A m_file-family lane's KROLE hit piece,
   a working branch) at image B's numbers, plus the two UBSan trap edges.

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 484-523, slow paths 723-734, error paths 883-885):
     0x868c8 a1 = -s4 = 4 i; 0x868cc-0x868d0 a0 = 0x211e0 (m_key.role, listing object 18); 0x868d4 a2 = ~a0
     0x868d8-0x868e0 s7 = 96(s1) = FB, s8 = 88(s1) = shadow(FB), s6 = 128(s1) = c + 0x2000
     0x868e4 `bltu a2,a1` -> unimp 0x86e84 (UBSan: m_key.role + 4 i wraps)
     0x868e8-0x868f0 a1 = 136(s1) & 3, `bnez a1` -> unimp 0x86e84 (UBSan: alignment of cur)
     0x868f4 a0 = a0 - s4 = &role[i]; 0x868f8-0x86904 the check of role[i] (load4; slow path 0x86c84, error path
       0x86f04)
     0x86908 a4 = 136(s1) = g = &c->seg[gi]; 0x8690c-0x86918 the check of g->role (store4; slow path 0x86c94, error
       path 0x86f08); 0x8691c a1 = role[i] = i; 0x86920 s4 = 511; 0x86928 g->role = a1
     0x8692c-0x86938 the check of g->role_set (store4; slow path 0x86ca4, error path 0x86f0c); 0x8693c s9 = 112(s1) = c
     0x86948 g->role_set = 1; 0x8694c-0x8695c a0 = g + 60, a2 = "%s" (object 14), a1 = 96, a3 = 64(s1) = &c->reading
     0x86960 jal snprintf; 0x86964 j 0x86c1c (KDONE).
   THE TRAP EDGES (each refuted at its branch, never stepped over):
     0x868e4 `bltu a2,a1`: the run stops at the branch (atom 20 = s4 has no fact); psrr_branch_tok splits; the taken
       edge is refuted from s4 = -4 i (KR_HIT_stmt) with i < 5 and a0 = m_key.role = 0x211e0 (VOBJS, mf_roles_obj):
       a1 = 4 i <= 16 < 2 ^ 64 - 1 - 0x211e0 = a2.
     0x868f0 `bnez a1`, a1 = cur & 3: decided by the executor from the fact of atom 37 (136(s1) = cur =
       mf_cur_ptr c (Some gi) = c + 256 gi), HPTR 4 (16-aligned), which holds since c mod 16 = 0 (mf_cx's
       m_file_pre); the taken edge is never a successor of the run.
   THE CHECKS (decided by the token executor from the shadow entries kh_SH; the slow paths are passes, the error paths
   0x86f04 / 0x86f08 / 0x86f0c are not reached):
     0x86900 load4 of role[i] at m_key.role + 4 i (atom 25): mkSHE 25 0 4, from mf_roles' sa_pinned (range
       addressable) and its place in the image (outside the shadow span).
     0x86918 store4 at g + 16 and 0x86938 store4 at g + 20 (atom 37): mkSHE 37 16 24, from mf_core's sa_addr of the
       mconf block (g + 24 <= c + 7960 < c + 9236).
   THE PROOF: kr_hit_run, one seed (m_file_sd.v mf_seed) with the frame cells made read-only and two regions added:
   g's 8 bytes [16, 24) at atom 37 (written) and role[i] at atom 25 (read-only, chunk = i, atom 52; mf_roles_now);
   one token run to the trap 0x868e4, its branch split, a run to 0x868f8, where a0 (a difference of two atoms) is
   replaced by atom 25 (s9's value), and one token run to the snprintf call. kr_snpret_kdone: the `j` at 0x86964
   from KDONE's statement (a run of one instruction, m_file_k.v mf_keep_run0). kr_s_hit joins them with snprintf's
   step (m_file_sn.v mf_snp_field_call): the block then holds m_upd mcc gi (ms_with_role i (mc_reading mcc))
   (mf_krole_enc.v kr_mconf_role), the cut facts are carried by m_file_k.v's mf_keep / mf_keep_cells / mf_loop_keep,
   the next line by mf_loop_next, and KDONE is applied at the FP state snprintf returns.
   Section hypotheses: VOBJS, SSP, RELRO, ASNPRINTF (section 2 of the KROLE piece plan; SSP and RELRO because the shared
   step m_file_sn.v asks SSP and its KRODJ, which m_file_k.v's mf_rod_now_j gives from RELRO). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtPFCmd RtPFSeg RtAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_mdl m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_krole_m mf_krole_enc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_sn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Notation ROLES := SegInstB.rolesA.

(* c->reading as sa_mconf holds it: a C string of fewer than 96 bytes, its bytes and NUL at c + MC_READING *)
Lemma kh_reading : forall (rd : reader) c mc, sa_mconf rd c mc ->
  sa_zs rd (c + seg_spec.MC_READING) (mc_reading mc ++ [0]) /\ (length (mc_reading mc) < 96)%nat /\
  ~ In 0 (mc_reading mc) /\ Forall (fun x => 0 <= x < 256) (mc_reading mc).
Proof.
intros rd c mc (bs & HB & HE).
destruct HE as (HL & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hf & Hlt & Hn0 & Hfz)).
unfold seg_spec.fldz, seg_spec.fld in Hf, Hfz. unfold seg_spec.SEG_M_SIZE in HL.
set (o := Z.to_nat seg_spec.MC_READING) in *. assert (Ho : Z.of_nat o = 9140) by reflexivity.
set (w := Z.to_nat 96) in *. assert (Hw : Z.of_nat w = 96) by reflexivity.
set (r := mc_reading mc) in *.
assert (HN : forall j, (j < S (length r))%nat -> nth j (r ++ [0]) 0 = bv_unsigned (nth (o + j) bs ZB0)).
{ intros j Hj. rewrite <- Hfz. rewrite nth_firstn. destruct (Nat.ltb_spec j (S (length r))) as [_|]; [|lia].
  unfold seg_spec.zs.
  rewrite (@List.nth_indep Z (map bv_unsigned (firstn w (skipn o bs))) j 0%Z (bv_unsigned ZB0))
    by (rewrite length_map, length_firstn, length_skipn; lia).
  rewrite map_nth. rewrite nth_firstn. destruct (Nat.ltb_spec j w) as [_|]; [|lia]. rewrite nth_skipn. reflexivity. }
split; [|split; [exact Hlt|split; [exact Hn0|]]].
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. rewrite HN by lia.
  replace (c + seg_spec.MC_READING + Z.of_nat j) with (c + Z.of_nat (o + j)) by (unfold seg_spec.MC_READING; lia).
  apply HB. lia.
- apply Forall_forall. intros x Hx. destruct (In_nth r x 0 Hx) as (j & Hj & Ex). subst x.
  rewrite <- (app_nth1 r [0] 0 Hj). rewrite HN by lia.
  pose proof (bv_unsigned_in_range 8 (nth (o + j) bs ZB0)) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

(* the points of the hit path *)
Definition KR_SUB : Z := AF_m_file + 0x7b8.      (* 0x868f8, after `sub a0,a0,s4` *)
Definition KR_SNPRET : Z := AF_m_file + 0x824.   (* 0x86964, snprintf's return: `j 0x86c1c` *)

(* the run's state: the frame cells read-only, g's role and role_set at atom 37 (written), role[i] at atom 25
   holding i (atom 52) *)
Definition kh_slots : YP09.region :=
  YP09.mkRegion (Some 2%nat) 16 216 16 16 (YP09.r_chunks (mf_r_slots true false [])).
Definition kh_g : YP09.region := YP09.mkRegion (Some 37%nat) 16 24 16 24 [].
Definition kh_role : YP09.region := YP09.mkRegion (Some 25%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 52 0))].
Definition kh_SH : list shent := [mkSHE 25 0 4; mkSHE 37 16 24].
Definition kh_facts : facts :=
  mkFacts ((52%nat, mkAF 0 4 0) :: (25%nat, HPTR 0) :: (37%nat, HPTR 4) :: f_atoms mf_facts) [] [].
Definition ss_kh : sstate := mkSS KR_HIT sr_mf [kh_g; kh_role; kh_slots] None kh_facts.

(* 4 bytes of the restricted memory read through the ASan reader *)
Lemma kh_sa_val4 : forall segs H mem a v,
val_mem segs (mrestrict H mem) a 4 v -> sa_val (aview segs H mem) a 4 v.
Proof.
intros segs H mem a v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map].
f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma kh_rolesB : ROLES = 0x211e0.
Proof. reflexivity. Qed.
(* 0x868f4 `sub a0,a0,s4` with s4 = -4 i: the engine's term for a0 is m_key.role + 4 i, atom 25's value *)
Lemma kh_sub_U : forall E (n20 n25 nr : nat) i R,
ew E n20 = Z_to_bv 64 (- (4 * Z.of_nat i)) -> ew E nr = Z_to_bv 64 R -> ew E n25 = Z_to_bv 64 (R + 4 * Z.of_nat i) ->
0 <= R -> R + 4 * Z.of_nat i < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff n20 0) (SLit (-1))) (SOff nr 0)) = sv_denot E (SOff n25 0).
Proof.
intros E n20 n25 nr i R H20 HR H25 HR0 HR1. apply U_inj.
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite H20, HR, H25.
rewrite !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.add_0_r, !Z.mod_mod by lia.
rewrite <- Z.mul_mod by lia. rewrite <- Z.add_mod by lia.
replace (- (4 * Z.of_nat i) * -1 + R) with (R + 4 * Z.of_nat i) by ring. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a register whose symbolic value is atom n + k *)
Lemma kh_reg : forall E ss (H : word -> bool) ms (r : bv 5) n k,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n k ->
getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + k).
Proof. intros E ss H ms r n k HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
Lemma kh_reg_lit : forall E ss (H : word -> bool) ms (r : bv 5) z,
st_ok SEGS E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof. intros E ss H ms r z HS Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hr. reflexivity. Qed.
(* a run of the hit's regions keeps every byte outside g's 8 bytes *)
Lemma kh_keep : forall E rs (H : word -> bool) (m m' : word -> option byte) g,
frame_of E rs (mrestrict H m) (mrestrict H m') ->
windows rs = [(Some 37%nat, 16, 24); (Some 25%nat, 0, 0); (Some 2%nat, 16, 16)] ->
base_val E (Some 37%nat) = g ->
forall a, 0 <= a < 2 ^ 64 -> ~ (g + 16 <= a < g + 24) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' g HF Hw Hg a Ha Hn.
apply (kept_of_frame E rs H m m' (fun x => g + 16 <= x < g + 24) HF); [|exact Ha | exact Hn].
intros b wlo whi x Hin Hr. rewrite Hw in Hin.
destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; [rewrite Hg in Hr; exact Hr | lia | lia].
Qed.
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the state at snprintf's entry (the jal executed) *)
Definition kr_call_st (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(pos : Z) (gi : nat) (line : Z) (i : nat) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem3 md3 0 /\
(forall a, 0 <= a < 2 ^ 64 ->
 ~ (seg_spec.mseg_addr (mv_c v) gi + 16 <= a < seg_spec.mseg_addr (mv_c v) gi + 24) ->
 rdW Wc mem3 a = rdW Wc memc a) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_ROLE) 4 (Z.of_nat i) /\
sa_val (rdW Wc mem3) (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_ROLE_SET) 4 1 /\
getr regs3 1 = Z_to_bv 64 (BASE + KR_SNPRET) /\
getr regs3 10 = w64 (seg_spec.mseg_addr (mv_c v) gi + seg_spec.MS_ROLE_FILE) /\ getr regs3 11 = w64 96 /\
getr regs3 12 = w64 (SegInstB.seg_litA_fz F_s) /\ getr regs3 13 = w64 (mv_c v + seg_spec.MC_READING) /\
mf_regs_at B v lyc pos regs3 /\ getr regs3 20 = w64 511 /\ getr regs3 27 = w64 (line + 1).

(* 0x868c8 to snprintf's entry *)
Lemma kr_hit_run : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z)
  (ok kl ov vl : nat) (k vv : list Z) (i : nat),
kr_cx B n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b B v regs1 ->
(i < 5)%nat ->
getr regs1 20 = w64 (- (4 * Z.of_nat i)) -> getr regs1 25 = w64 (ROLES + 4 * Z.of_nat i) ->
getr regs1 27 = w64 (line + 1) ->
(forall regs3 mem3 md3, kr_call_st v lyc Sc Wc memc pos gi line i regs3 mem3 md3 ->
  SRr SEGS Wc (mkCfg (mkst regs3 (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) mem3 (seg_rom SEGS)) md3)
    (MF_POST B v)) ->
mf_at B v Wc regs1 memc mdc KR_HIT.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv i CXK RB Hi R20 R25 R27 KC.
destruct CXK as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & KV & FIN & NP & HIEQ).
unfold mf_at.
pose proof RB as (R2 & R3 & R4 & R8 & R9 & R18 & R19).
assert (RBS : mf_regs_base v regs1) by (repeat split; assumption).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _ & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof CORE as (HJ & HPerm & _ & _ & _ & _ & HMC & HMA & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
unfold mf_cur_ok in LCUR.
pose proof HMC as (bs & _ & (HL & HL32 & _)).
pose proof HMA as (CA0 & CA1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (c := mv_c v) in *.
set (g := seg_spec.mseg_addr c gi).
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hgi32 : (gi < 32)%nat) by lia.
assert (Hcur : 0 <= mf_cur_ptr c (Some gi) < 2 ^ 64)
  by (unfold mf_cur_ptr; fold g; unfold seg_spec.SEG_M_SIZE in *; lia).
set (xs := [Z.of_nat i]).
(* the seed: the frame cells (cells = true), no 152(s1), no extra chunk *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) 0 xs KR_HIT true false []
  false false [] false CX CORE RBS (fun _ => CELLS) Hcur (fun H => False_ind _ (diff_false_true H)) ltac:(lia)
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
set (E := mfE regs1 v lyc pos (Some gi) 0 xs) in *.
assert (E52 : ew E 52 = Z_to_bv 64 (Z.of_nat i)) by exact (mfE_xs regs1 v lyc pos (Some gi) 0 xs 0 ltac:(unfold A_TEXT; lia)).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 xs) (Z_to_bv 64 0))
  by (intros; apply mfE_extra; assumption).
pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E33, E34, E36, E37. fold c in E33, E37. unfold mf_cur_ptr in E37. fold g in E37.
assert (E2 : ew E 2 = getr regs1 2) by exact (mfE_reg regs1 v lyc pos (Some gi) 0 xs 2 2%bv eq_refl).
assert (E20 : ew E 20 = getr regs1 20) by exact (mfE_reg regs1 v lyc pos (Some gi) 0 xs 20 20%bv eq_refl).
assert (E25 : ew E 25 = getr regs1 25) by exact (mfE_reg regs1 v lyc pos (Some gi) 0 xs 25 25%bv eq_refl).
rewrite R25 in E25. rewrite R2 in E2. rewrite R20 in E20. unfold w64 in E20.
assert (HS1 : st_ok_pi SEGS VAL E (mkSS KR_HIT sr_mf [kh_slots] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KR_HIT)) memc (seg_rom SEGS)))).
{ refine (st_ok_pi_submem E _ _ [kh_slots] HS0 _ ltac:(vm_compute; reflexivity)).
  cbn [ss_mem ss_mf]. unfold mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, kh_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks mf_r_slots].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros ch Hch. exact Hch. }
clear HS0.
(* where things lie: the mconf block, s1, role[i] *)
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1r : alloc_ceiling + 8000 <= mf_s1 (mv_sp v) <= 2 ^ 47) by (destruct Ss1 as [E1 | E1]; rewrite E1; lia).
assert (Hroles : ROLES = 0x211e0) by exact kh_rolesB.
pose proof CX as (_ & _ & _ & _ & _ & (HRP & _) & _).
pose proof (mf_roles_now B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (_ & _ & HRV).
assert (Hfin : (gi < length (mc_seg (mf_final v)))%nat).
{ pose proof (kr_fin_grows mcc gi k vv line rest HIEQ LCUR) as (G1 & _). rewrite FIN in G1.
  rewrite (kr_role_seg_len mcc gi k vv (line + 1) HIEQ) in G1. lia. }
unfold w64 in E2, E25.
assert (B2 : base_val E (Some 2%nat) = mf_s1 (mv_sp v)) by (cbn [base_val]; rewrite E2; apply unsigned_lit_small; lia).
assert (B25 : base_val E (Some 25%nat) = ROLES + 4 * Z.of_nat i)
  by (cbn [base_val]; rewrite E25; apply unsigned_lit_small; lia).
assert (B37 : base_val E (Some 37%nat) = g) by (cbn [base_val]; rewrite E37; apply unsigned_lit_small; lia).
(* the facts of atoms 37 (g, 16-aligned: c mod 16 = 0), 25 (&role[i]), 52 (i) *)
unfold seg_spec.SEG_M_SIZE in *.
assert (Hg16 : g mod 16 = 0).
{ rewrite Hg. replace (c + 256 * Z.of_nat gi) with (c + 16 * Z.of_nat gi * 16) by ring.
  rewrite Z_mod_plus_full. exact Hc16. }
assert (F37 : afact_ok E 37 (HPTR 4)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E37, unsigned_lit_small by lia.
  change (2 ^ 4) with 16. split; [lia|]. split; [exact Hg16|]. lia. }
assert (F25 : afact_ok E 25 (HPTR 0)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity|]. lia. }
assert (F52 : afact_ok E 52 (mkAF 0 4 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E52, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (HS2 : st_ok_pi SEGS VAL E (mkSS KR_HIT sr_mf [kh_slots] None kh_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KR_HIT)) memc (seg_rom SEGS))))
  by exact (st_ok_pi_add_fact E _ _ 52 _ (st_ok_pi_add_fact E _ _ 25 _ (st_ok_pi_add_fact E _ _ 37 _ HS1 F37) F25) F52).
clear HS1.
(* role[i] (read-only, holding i) and g's role / role_set (written) *)
assert (ROK : region_ok SEGS E (mrestrict (w_H Wc) memc) kh_role).
{ unfold region_ok, kh_role. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B25.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (ROLES + 4 * Z.of_nat i) 0 4 (SOff 52 0) (Z.of_nat i)).
  - cbn [sv_denot]. rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity. rewrite H32. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H Wc) memc _ _ (HRV i Hi)). }
assert (GOK : region_ok SEGS E (mrestrict (w_H Wc) memc) kh_g).
{ unfold region_ok, kh_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (g + o) ltac:(lia))). }
assert (HS3 : st_ok_pi SEGS VAL E (mkSS KR_HIT sr_mf [kh_role; kh_slots] None kh_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KR_HIT)) memc (seg_rom SEGS)))).
{ apply (st_ok_pi_add_region E _ _ kh_role HS2 eq_refl ROK).
  apply all_disjoint_of_extents. unfold kh_role, kh_slots, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi ss_mem]. rewrite B25, B2.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
assert (HS : st_ok_pi SEGS VAL E ss_kh
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KR_HIT)) memc (seg_rom SEGS)))).
{ apply (st_ok_pi_add_region E _ _ kh_g HS3 eq_refl GOK).
  pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mbc HAR Hbc) as Hoff. unfold off_img, kImgEnd in Hoff.
  apply all_disjoint_of_extents. unfold kh_g, kh_role, kh_slots, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi ss_mem]. rewrite B37, B25, B2.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
clear HS2 HS3.
(* the shadow entries of the three inline checks: role[i] (4 bytes), g->role and g->role_set *)
assert (SHOK : sh_ok SEGS (SOff 32 0) kh_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, kh_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - pose proof (HRP lyc Sc Wc memc mdc HAR) as (_ & _ & _ & HRA & _).
    apply (mf_she_at E Wc memc 25 (ROLES + 4 * Z.of_nat i) 4 (mfE_U32 regs1 v lyc pos (Some gi) 0 xs) E25);
      [lia | lia | |].
    + eapply range_addressable_sub; [exact HRA | lia | lia].
    + intros x Hx. unfold SHADOW_OFF. lia.
  - pose proof HMA as (_ & _ & _ & HRAc & _).
    apply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 32 0) 37 c seg_spec.SEG_M_SIZE g 16 24 HRAc
      (mfE_U32 regs1 v lyc pos (Some gi) 0 xs) (U_atom E 37 g E37 ltac:(lia)));
      [unfold seg_spec.SEG_M_SIZE in *; lia | unfold seg_spec.SEG_M_SIZE in *; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. apply (mf_blk_app B v CX). unfold seg_spec.SEG_M_SIZE in *. lia. }
(* the writes the journal allows: g's 8 bytes lie in M_FILE_FP's entries and in the mconf block's heap block *)
assert (AWR : forall E', ew E' 37 = Z_to_bv 64 g ->
  awr_ok SEGS B E' [kh_g; kh_role; kh_slots] SegInstB.STK_m_file (mv_sp v) (M_FILE_FP c (mv_k0 v) (mf_final v))
    (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)]).
{ intros E' E37'.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat g);
    [reflexivity | rewrite E37'; apply unsigned_lit_small; lia | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi kh_g] in Ha. right; left. split.
    + exists (c, seg_spec.mseg_addr c (length (mc_seg (mf_final v)))). split; [left; reflexivity|].
      cbn [fst snd]. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. lia.
    + exists bc, mbc. split; [exact Hbc | unfold seg_spec.SEG_M_SIZE in *; lia].
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EA : ew E 259 = Z_to_bv 64 ROLES).
{ unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) 0 xs 259 ltac:(unfold A_TEXT, A_LIM; lia)).
  change 259%nat with (A_OBJ MF_ROLES_OBJ). rewrite <- (mf_roles_obj VOBJS). reflexivity. }
(* 0x868c8 .. 0x868e0: a1 = 4 i, a0 = m_key.role, a2 = ~a0, the restores of s7 / s8 / s6; the run stops at the
   trap branch 0x868e4 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ exact (AWR E E37). }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 0x868e4 taken: the UBSan trap (m_key.role + 4 i wraps), refuted: a1 = 4 i <= 16 < 2 ^ 64 - 1 - 0x211e0 = a2 *)
  exfalso.
  rewrite branch_ltu_U in Hc.
  repeat first [rewrite U_SAlu in Hc | rewrite U_SMd in Hc | rewrite U_SOff in Hc | rewrite U_SLit in Hc].
  rewrite ?E20, ?EA in Hc. rewrite ?Hroles in Hc. rewrite ?Z_to_bv_unsigned in Hc.
  clear - Hc Hi.
  destruct i as [|[|[|[|[|i]]]]]; [..|lia]; vm_compute in Hc; discriminate Hc.
- (* 0x868e4 not taken; 0x868e8 .. 0x868f4: a1 = cur & 3 = 0 (the trap 0x868f0 is decided by the fact HPTR 4 of
     atom 37), a0 = m_key.role - s4; the run stops at 0x868f8 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KR_SUB.
  { exact (AWR E E37). }
  (* a0 = atom 25 (&role[i], s9's value) *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_restrict_reg (w_H Wc) E ssx msx 10%bv HS) as R10;
    let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in R10
  end.
  rewrite (kh_sub_U E 20 25 259 i ROLES E20 EA E25 ltac:(lia) ltac:(lia)) in R10.
  pose proof (st_ok_pi_set_reg E _ _ 10%bv (SOff 25 0) HS
    ltac:(intros Hx; apply (f_equal bv_unsigned) in Hx; vm_compute in Hx; discriminate Hx) R10) as HS'.
  clear HS R10. rename HS' into HS.
  (* 0x868f8 .. 0x86960: the three checks, the load of role[i], the two stores, snprintf's arguments; the jal *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { exact (AWR E E37). }
  (* the state at snprintf's entry: its environment agrees with E below the token atoms *)
  lazymatch goal with HSx : st_ok _ ?Ex _ (restrict _ ?mB) |- _ => set (Ek := Ex) in *; rename mB into ms3 end.
  assert (HAE : env_agree 1024 E Ek) by (unfold Ek; env_agree_chain (env_agree_refl 1024 E)).
  assert (EE : forall n0, (n0 < 1024)%nat -> ew Ek n0 = ew E n0) by (intros n0 Hn0; exact (proj1 HAE n0 Hn0)).
  pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
  assert (HF8 : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
  { assert (Hfin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin1) as (F1 & F2 & _).
    change (fs_frame_bytes 1) with 128 in F2. lia. }
  assert (HFd : 0 <= frame_addr lyc 1 pos / 8 <= 2 ^ 44)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  (* the registers at the jal *)
  lazymatch goal with HSx : st_ok _ Ek ?ssx (restrict _ ms3) |- _ =>
    assert (QR : forall (r : bv 5) n0 k0, sr_get (ss_regs ssx) r = SOff n0 k0 -> (n0 < 1024)%nat ->
      getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0))
      by (intros r n0 k0 Hr Hn0; rewrite <- (EE n0 Hn0); exact (kh_reg Ek ssx (w_H Wc) ms3 r n0 k0 HSx Hr));
    assert (QL : forall (r : bv 5) z, sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms3) r = Z_to_bv 64 z)
      by (intros r z Hr; exact (kh_reg_lit Ek ssx (w_H Wc) ms3 r z HSx Hr))
  end.
  assert (QA : forall (r : bv 5) n0 x k0, ew E n0 = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + k0) -> getr (ms_regs ms3) r = Z_to_bv 64 (x + k0))
    by (intros r n0 x k0 Hn0 Hx Hr; rewrite Hr, Hn0, unsigned_lit_small by exact Hx; reflexivity).
  assert (QS : forall (r : bv 5) n0, ew E n0 = getr regs1 r ->
    getr (ms_regs ms3) r = Z_to_bv 64 (bv_unsigned (ew E n0) + 0) -> getr (ms_regs ms3) r = getr regs1 r)
    by (intros r n0 Hn0 Hr; rewrite Hr, Z.add_0_r, Hn0; apply Z_to_bv_bv_unsigned).
  assert (HKS : KR_SNPRET = 7076) by reflexivity.
  pose proof (QR 1%bv 240%nat KR_SNPRET eq_refl ltac:(lia)) as Q1.
  rewrite (img_env_codeptr E HEI KR_SNPRET) in Q1.
  pose proof (QA 2%bv 2%nat _ 0 E2 ltac:(lia) (QR 2%bv 2%nat 0 eq_refl ltac:(lia))) as Q2.
  pose proof (QS 3%bv 3%nat (mfE_reg regs1 v lyc pos (Some gi) 0 xs 3 3%bv eq_refl) (QR 3%bv 3%nat 0 eq_refl ltac:(lia))) as Q3.
  pose proof (QS 4%bv 4%nat (mfE_reg regs1 v lyc pos (Some gi) 0 xs 4 4%bv eq_refl) (QR 4%bv 4%nat 0 eq_refl ltac:(lia))) as Q4.
  pose proof (QS 8%bv 8%nat (mfE_reg regs1 v lyc pos (Some gi) 0 xs 8 8%bv eq_refl) (QR 8%bv 8%nat 0 eq_refl ltac:(lia))) as Q8.
  pose proof (QA 9%bv 2%nat _ 0 E2 ltac:(lia) (QR 9%bv 2%nat 0 eq_refl ltac:(lia))) as Q9.
  pose proof (QA 10%bv 37%nat _ 60 E37 ltac:(lia) (QR 10%bv 37%nat 60 eq_refl ltac:(lia))) as Q10.
  pose proof (QL 11%bv 96 eq_refl) as Q11.
  pose proof (QR 12%bv 255%nat 0 eq_refl ltac:(lia)) as Q12.
  pose proof (QA 13%bv 33%nat _ 9140 E33 ltac:(lia) (QR 13%bv 33%nat 9140 eq_refl ltac:(lia))) as Q13.
  pose proof (QA 18%bv 32%nat _ 0 E32 ltac:(unfold SHADOW_OFF; lia) (QR 18%bv 32%nat 0 eq_refl ltac:(lia))) as Q18.
  pose proof (QS 19%bv 19%nat (mfE_reg regs1 v lyc pos (Some gi) 0 xs 19 19%bv eq_refl) (QR 19%bv 19%nat 0 eq_refl ltac:(lia))) as Q19.
  pose proof (QL 20%bv 511 eq_refl) as Q20.
  pose proof (QA 22%bv 33%nat _ 8192 E33 ltac:(lia) (QR 22%bv 33%nat 8192 eq_refl ltac:(lia))) as Q22.
  pose proof (QA 23%bv 34%nat _ 0 E34 ltac:(lia) (QR 23%bv 34%nat 0 eq_refl ltac:(lia))) as Q23.
  pose proof (QA 24%bv 36%nat _ 0 E36 ltac:(unfold SHADOW_OFF; lia) (QR 24%bv 36%nat 0 eq_refl ltac:(lia))) as Q24.
  pose proof (QA 25%bv 33%nat _ 0 E33 ltac:(lia) (QR 25%bv 33%nat 0 eq_refl ltac:(lia))) as Q25.
  pose proof (QS 27%bv 27%nat (mfE_reg regs1 v lyc pos (Some gi) 0 xs 27 27%bv eq_refl) (QR 27%bv 27%nat 0 eq_refl ltac:(lia))) as Q27.
  rewrite !Z.add_0_r in Q2, Q9, Q18, Q23, Q24, Q25.
  (* the bytes: kept outside g's 8 bytes; g->role = i, g->role_set = 1 *)
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 16 <= a < g + 24) -> rdW Wc (ms_mem ms3) a = rdW Wc memc a).
  { intros a Ha Hna.
    lazymatch goal with
    | H1 : frame_of _ ?r1 (mrestrict _ memc) (mrestrict _ (ms_mem ?mA)),
      H2 : frame_of _ ?r2 (mrestrict _ (ms_mem ?mA)) (mrestrict _ (ms_mem ?mB)),
      H3 : frame_of _ ?r3 (mrestrict _ (ms_mem ?mB)) (mrestrict _ (ms_mem ms3)) |- _ =>
      rewrite (kh_keep _ r3 (w_H Wc) _ _ g H3 ltac:(vm_compute; reflexivity) B37 a Ha Hna);
      rewrite (kh_keep _ r2 (w_H Wc) _ _ g H2 ltac:(vm_compute; reflexivity) B37 a Ha Hna);
      exact (kh_keep _ r1 (w_H Wc) _ _ g H1 ltac:(vm_compute; reflexivity) B37 a Ha Hna)
    end. }
  assert (UG : bv_unsigned (ew Ek 37) = g) by (rewrite (EE 37%nat ltac:(lia)), E37; apply unsigned_lit_small; lia).
  lazymatch goal with HSx : st_ok _ Ek ?ssx (restrict _ ms3) |- _ =>
    pose proof (st_ok_region_nth Ek ssx (restrict (w_H Wc) ms3) 0 _ HSx eq_refl) as HR0 end.
  pose proof (field_of_region Ek _ 37 g _ _ _ _ _ 16 4%N (SOff 52 0) (Z.of_nat i) HR0 UG
    ltac:(repeat (first [left; reflexivity | right]))
    ltac:(cbn [sv_denot]; rewrite (EE 52%nat ltac:(lia)), E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity; rewrite H32; lia) ltac:(cbn; lia)) as VR.
  pose proof (field_of_region Ek _ 37 g _ _ _ _ _ 20 4%N (SLit 1) 1 HR0 UG
    ltac:(repeat (first [left; reflexivity | right]))
    eq_refl ltac:(assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity; rewrite H32; lia) ltac:(cbn; lia)) as VRS.
  change (N.to_nat 4) with 4%nat in VR, VRS.
  (* the call *)
  pmkst HS.
  assert (HFs : SegInstB.seg_litA_fz F_s = 0x21080) by (vm_compute; reflexivity).
  apply KC. unfold kr_call_st, w64.
  split; [exact HJ|].
  split; [exact KP|].
  split; [unfold seg_spec.MS_ROLE; exact (kh_sa_val4 SEGS (w_H Wc) (ms_mem ms3) _ _ VR)|].
  split; [unfold seg_spec.MS_ROLE_SET; exact (kh_sa_val4 SEGS (w_H Wc) (ms_mem ms3) _ _ VRS)|].
  split; [exact Q1|].
  split; [rewrite Q10; reflexivity|].
  split; [rewrite Q11; reflexivity|].
  split.
  { rewrite Q12. unfold E. rewrite (mfE_img regs1 v lyc pos (Some gi) 0 xs 255 ltac:(unfold A_TEXT, A_LIM; lia)).
    change 255%nat with (A_OBJ 14). rewrite <- (mf_lit_obj VOBJS F_s 14 ltac:(left; reflexivity)).
    rewrite HFs, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
  split; [rewrite Q13; reflexivity|].
  split.
  { unfold mf_regs_at, mf_regs_ex, w64. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q23, Q24, Q19, Q22, Q25.
    split; [split; [reflexivity|] |].
    - split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [reflexivity|].
      split; [reflexivity|]. split; reflexivity.
    - split; [exact R19|]. split; reflexivity. }
  split; [rewrite Q20; reflexivity|].
  rewrite Q27. exact R27.
Qed.

(* 0x86964 `j 0x86c1c`: KDONE's statement holds one instruction earlier *)
Lemma kr_snpret_kdone : forall n v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z),
MF_KDONE_stmt B n ->
mf_cx B v -> mf_ls v lyc Sc -> sa_frm0 ->
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur -> mf_regs_at B v lyc pos regs1 ->
(length rest < n)%nat -> mf_loop v Wc memc mcc cur line p rest ->
fst (m_lines (mcc, cur) line (lines rest)) = mf_final v ->
mf_np v memc Wc p -> getr regs1 27 = w64 line -> getr regs1 20 = w64 511 ->
mf_at B v Wc regs1 memc mdc KR_SNPRET.
Proof.
intros n v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest KD CX LS FRM CORE CELLS RA Hn LOOP FIN NP R27 R20.
unfold mf_at.
set (E := Eimg (Ereg regs1 [Z_to_bv 64 SHADOW_OFF])).
assert (HS : st_ok_pi SEGS VAL E (mkSS KR_SNPRET sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + KR_SNPRET)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; [exact I | exact I]]. exact I. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg regs1 [Z_to_bv 64 SHADOW_OFF]) E)
  by (split; [intros n0 Hn0; unfold E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
pose proof CORE as (HJ & _).
paj_run_to_tok RUNTO HS HJ SHOK Bspan MF_KDONE.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  apply awr_ok_nil. }
assert (HK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27]%bv -> getr (ms_regs ms) r = getr regs1 r).
{ pose proof (regs_kept_of_st_ok_pi E _ _ regs1 _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 27]%bv HS HA0
    ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK. exact HK. }
assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rr & Hin & _); exact Hin).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur (ms_mem ms) _ CX CORE CELLS HJ EQV)
  as (C1 & C2 & C3 & C4).
pmkst HS.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
refine (KD v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos mcc cur line p rest CX LS FRM C1 C2 _ Hn (C4 _ _ _ _ _ LOOP)
  FIN (C3 _ NP) _ _).
- unfold mf_regs_at, mf_regs_ex. rewrite !HK by (cbv [In]; tauto).
  repeat split; assumption.
- rewrite HK by (cbv [In]; tauto). exact R27.
- rewrite HK by (cbv [In]; tauto). exact R20.
Qed.
End e.
End f.
End d.

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
(* the shared Section hypotheses this piece uses (section 2 of the KROLE piece plan; SSP and RELRO for m_file_sn.v) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstB.gotwA SegInstB.guardA.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B
  RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR (SIGMA SS___interceptor_trampoline_snprintf)
  RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.

(* KR_HIT 0x868c8: the role stores, snprintf of c->reading into g->role_file, `j` to KDONE *)
Lemma kr_s_hit : forall n, MF_KDONE_F B n -> KR_HIT_stmt B n.
Proof.
intros n KD. unfold KR_HIT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv i CXK RB Hi HROLE R20 R25 R27.
pose proof CXK as (CX & LS & FRM & CORE & CELLS & Hn & Hne & LOOP & KV & FIN & NP & HIEQ).
apply (kr_hit_run B VOBJS n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv i CXK RB Hi R20 R25 R27).
intros regs3 mem3 md3 (HJ3 & KP3 & VR3 & VRS3 & Q1 & Q10 & Q11 & Q12 & Q13 & RA3 & Q20 & Q27).
(* where things lie *)
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _).
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HJ3 as (HAR3 & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
unfold mf_cur_ok in LCUR.
pose proof HMC as (bs0 & _ & (_ & HL32 & _)).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
assert (HF8 : 4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling).
{ assert (Hfin1 : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin1) as (F1 & F2 & _).
  change (fs_frame_bytes 1) with 128 in F2. lia. }
assert (HFd : 0 <= frame_addr lyc 1 pos / 8 /\ frame_addr lyc 1 pos / 8 * 8 <= frame_addr lyc 1 pos)
  by (split; [apply Z.div_pos; lia | pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)); lia]).
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hs1r : mv_sp v - 336 <= mf_s1 (mv_sp v) <= mv_sp v - 320) by (destruct Ss1 as [E1|E1]; rewrite E1; lia).
assert (HKS : KR_SNPRET = 7076) by reflexivity.
assert (HKK : RtPFSeg.SEG_SNP_K = 8192) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
set (c := mv_c v) in *.
set (s1 := mf_s1 (mv_sp v)) in *.
set (g := seg_spec.mseg_addr c gi) in *.
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hgi32 : (gi < 32)%nat) by lia.
unfold seg_spec.SEG_M_SIZE in *.
(* c->reading, at the call state too *)
destruct (kh_reading _ _ _ HMC) as (HZR & Hrl & Hr0 & Hrb).
set (r := mc_reading mcc) in *.
assert (Hfin : (gi < length (mc_seg (mf_final v)))%nat).
{ pose proof (kr_fin_grows mcc gi k vv line rest HIEQ LCUR) as (G1 & _). rewrite FIN in G1.
  rewrite (kr_role_seg_len mcc gi k vv (line + 1) HIEQ) in G1. lia. }
assert (HZR3 : sa_zs (rdW Wc mem3) (c + seg_spec.MC_READING) (r ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  rewrite KP3; [exact (HZR j ltac:(rewrite length_app; cbn [length]; lia)) | unfold seg_spec.MC_READING; lia
    | unfold seg_spec.MC_READING; lia]. }
assert (HSA3 : sa_addr (rdW Wc mem3) c 9236).
{ destruct HMA as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR3 Hbc); lia. }
assert (HST3 : sa_tail (rdW Wc mem3) (c + 9236 - 1)).
{ intros x Hx. pose proof (Z.mod_pos_bound (c + 9236 - 1) 8 ltac:(lia)).
  rewrite KP3; [exact (HMT x Hx) | lia | lia]. }
(* 0x86960: snprintf(g->role_file, 96, "%s", c->reading) *)
pose proof RA3 as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25').
apply (mf_snp_field_call B SSP ASNPRINTF (mf_rod_now_j B RELRO) (mf_lit_now_j B) v lyc Sc Wc regs3 mem3 md3 pos
  gi r seg_spec.MS_ROLE_FILE KR_SNPRET (or_introl eq_refl) CX LS FRM HJ3 HPerm HSA3 HST3 HZR3 Hrl Hr0 Hgi32 Hfin
  R2 R3 R4 Q1 ltac:(rewrite HKS; lia) ltac:(rewrite HKS; reflexivity) Q10 Q11 Q12 Q13).
intros fx1 regs2 mem2 md2 Hfx HJ2 HP2 HZF HK2.
rewrite HKK in HK2. fold c s1 in HK2, HZF. fold g in HK2, HZF.
set (d := g + seg_spec.MS_ROLE_FILE) in *.
assert (Hd : d = g + 60) by reflexivity.
(* what 0x868c8 .. 0x86960 and snprintf wrote: g's role / role_set, snprintf's window, the field *)
set (RW := fun a => (g + 16 <= a < g + 24) \/ (s1 - 8192 <= a < s1) \/ (d <= a < d + Z.of_nat (length r) + 1)).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha HR. rewrite (HK2 a Ha); [apply KP3; [exact Ha|] | |]; intros Hc; apply HR; unfold RW; tauto. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a [Ha | [Ha | Ha]]; unfold mf_rw, seg_spec.SEG_M_SIZE; rewrite HSTK; fold s1 c.
  - right; left. lia.
  - left. lia.
  - right; left. lia. }
assert (RWS : mf_rws v RW).
{ intros a HR Ha. exfalso. fold s1 in Ha. destruct HR as [H | [H | H]]; lia. }
assert (NRW_lo : forall a, a < alloc_ceiling -> ~ (c <= a < c + 9236) -> ~ RW a).
{ intros a H1 H2 [H | [H | H]]; lia. }
assert (NRW_hi : forall a, s1 <= a -> ~ RW a).
{ intros a H1 [H | [H | H]]; lia. }
(* the block after the three stores holds mcc' *)
set (mcc' := m_upd mcc gi (ms_with_role (Z.of_nat i) r)).
assert (MC2 : sa_mconf (rdW Wc mem2) c mcc').
{ apply (kr_mconf_role (rdW Wc memc) (rdW Wc mem2) c mcc gi (Z.of_nat i) r HMC LCUR ltac:(lia) Hr0 Hrb Hrl).
  unfold kr_role_bytes. cbv zeta. fold g. fold d.
  split; [|split; [|split]].
  - intros kk Hkk. unfold seg_spec.MS_ROLE in *. rewrite HK2; [exact (VR3 kk Hkk) | lia | lia | lia].
  - intros kk Hkk. unfold seg_spec.MS_ROLE_SET in *. rewrite HK2; [exact (VRS3 kk Hkk) | lia | lia | lia].
  - exact HZF.
  - intros a Ha H1 H2. unfold seg_spec.SEG_M_SIZE, seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET in *.
    apply K; [lia|]. intros [H | [H | H]]; lia. }
(* every cut fact at the return *)
assert (VKEEP : forall a nb x, 0 <= a -> a + Z.of_nat nb <= 2 ^ 64 -> (forall kk, 0 <= kk < Z.of_nat nb -> ~ RW (a + kk)) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) a nb x -> val_mem SEGS (mrestrict (w_H Wc) mem2) a nb x)
  by (intros a nb x H0 H1 H2 V; exact (mf_val_keep Wc Wc memc mem2 RW a nb x K H0 H1 H2 V)).
assert (CORE2 : mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_ON mcc').
{ apply (mf_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Sc Wc mem2 md2 RW MF_LOW_ON mcc' CX CORE HJ2
    (Permutation_refl _) K RWok); [| |exact MC2].
  - intros ii Hii. apply VKEEP; [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH ii Hii)].
    intros kk Hkk. change (Z.of_nat 1) with 1 in Hkk. apply NRW_lo; unfold SHADOW_OFF in *; lia.
  - apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact V120].
    intros kk Hkk. apply NRW_hi. lia. }
assert (CELLS2 : mf_cells v lyc pos mem2 Wc (Some gi)).
{ apply (mf_keep_cells B v lyc pos Wc Wc memc mem2 RW (Some gi) (Some gi) CX K RWS CELLS).
  pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
  apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact V136].
  intros kk Hkk. apply NRW_hi. lia. }
assert (LOOP2 : mf_loop v Wc mem2 mcc (Some gi) line p rest)
  by exact (mf_loop_keep B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc Sc Wc mem2 md2 RW mcc (Some gi) line p rest CX CORE HJ2
    (Permutation_refl _) K RWok LOOP).
assert (LOOPn : mf_loop v Wc mem2 mcc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)).
{ eapply mf_loop_next; [exact LOOP2 | exact Hne | | | |].
  - unfold mcc', m_upd, m_set_segs. cbn [mc_refused]. lia.
  - unfold mcc', m_upd, m_set_segs. cbn [mc_overflow]. lia.
  - unfold mcc', m_upd, m_set_segs. cbn [mc_kept]. lia.
  - unfold mf_cur_ok, mcc', m_upd, m_set_segs. cbn [mc_seg]. rewrite mf_upd_nth_length. exact LCUR. }
assert (NP2 : mf_np v mem2 Wc (mf_next p rest)).
{ unfold mf_np, mf_slot in NP |- *. apply VKEEP; [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros kk Hkk. apply NRW_hi. lia. }
assert (FIN2 : fst (m_lines (mcc', Some gi) (line + 1) (lines (mf_rest rest))) = mf_final v).
{ rewrite <- FIN. unfold mf_fin. rewrite (kr_mk_disp_role mcc gi k vv (line + 1) HIEQ), HROLE.
  rewrite (kr_snprintf_s_reading (mc_reading mcc) Hr0 Hrl). reflexivity. }
assert (Hn2 : (length (mf_rest rest) < n)%nat).
{ destruct (mf_break_snd rest) as (_ & Bk2 & _). pose proof (Bk2 Hne) as Bk. unfold mf_rest. lia. }
assert (G : forall rr, acallee_saved rr -> getr regs2 (Z_to_bv 5 rr) = getr regs3 (Z_to_bv 5 rr)) by exact HP2.
assert (P20 : getr regs2 20 = getr regs3 20) by exact (G 20 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs2 27 = getr regs3 27) by exact (G 27 ltac:(unfold acallee_saved; lia)).
exact (kr_snpret_kdone (fx := fx1) B n v lyc Sc Wc regs2 mem2 md2 pos mcc' (Some gi) (line + 1) (mf_next p rest)
  (mf_rest rest) (KD fx1) CX LS (fxrel_frm0 fx fx1 FRM Hfx) CORE2 CELLS2 (mf_regs_keep B v lyc pos regs3 regs2 RA3 HP2)
  Hn2 LOOPn FIN2 NP2 ltac:(rewrite P27; exact Q27) ltac:(rewrite P20; exact Q20)).
Qed.
End e2.
End f2.
End d2.
About kr_s_hit.
Print Assumptions kr_s_hit.
