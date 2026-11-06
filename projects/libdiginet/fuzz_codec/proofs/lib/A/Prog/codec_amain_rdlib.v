(* The pieces the reader segments RD0 .. RD11 of the image-A walk of LLVMFuzzerTestOneInput share
   (lib/A/Prog/codec_amain_inv.v, seg_rd_run): the executor state at a reader cut, the write windows a reader
   uses, and the step from the executor state at RUN (0x820d0) to the cut inv_run.

   The state (rd_ss pc lo hi AF): the registers of codec_amain_st.v (am_sregs), the regions
     k      the call record, F + 176 .. F + 360 (atom 33 = F), writable in [176 + lo, 176 + hi): the fields the
            reader stores (a at 24, b at 28, c at 32, the bytes at 40 ..);
     the empty save area, the spills 16(sp1) .. 120(sp1) and the cursor 152(sp1) / 160(sp1) of am_regs (the
     .got slot of the shadow-offset cell and the cell itself are dropped: s4 already holds the offset);
   the atom facts of am_atoms, then the segment's own AF (the input bytes it reads, atoms 37 ..).
   The k window lies inside the frame, whose atom fact does not keep it off the shadow band, so every run
   carries the shadow entry rd_SH = [mkSHE 33 176 360] (k's 184 bytes are marked usable at a reader cut).

   The zone a reader writes (rd_zone): the cursor [sp1 + 152, sp1 + 168) and the k window. A run's kept fact
   is stated over it; it is apart from the bytes mcommon keeps (am_keepzone) and from the frame's shadow. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the record a reader leaves ================================ *)
(* k as HEAD leaves it with the reader's a, b, c, delta and bytes stored (n stays 0) *)
Definition rdk (kind pv dv a b c d : Z) (bytes : list Z) : kcallZ :=
mkKcallZ kind pv dv a b c d bytes 0 0 fa5 fa5 0 (repeat 0 24) 0 0 0.
Lemma rdk_rd : forall kind pv dv, k_rdZ kind pv dv = rdk kind pv dv 0 0 0 0 (repeat 0 24).
Proof. reflexivity. Qed.

(* the record run() is called with, from the reader's ranges *)
Lemma rd_enc_ok : forall kind pv dv a b c d bytes od,
0 <= kind <= 11 -> pd_okA pv dv od -> reader_ok kind a b c d bytes 0 ->
enc_okZ (rdk kind pv dv a b c d bytes) od.
Proof.
intros kind pv dv a b c d bytes od Hk Hpd Hr. unfold enc_okZ, rdr_kZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c
  kz_delta kz_bytes kz_n kz_before kz_out rdk].
split; [exact Hk|]. split; [exact Hpd|]. split; [exact Hr|]. split; reflexivity.
Qed.

(* ================================ the state ================================ *)
Definition rd_base : smem := [stack_region 0; am_spill_region; am_cur_region].
Definition rd_krg (lo hi : Z) (cs : list YP09.chunk) : YP09.region := am_frame_region 176 360 (176 + lo) (176 + hi) cs.
Definition rd_ss (pc lo hi : Z) (cs : list YP09.chunk) (AF : list (nat * afact)) : sstate :=
mkSS pc am_sregs (rd_krg lo hi cs :: rd_base) None (mkFacts (am_atoms ++ AF) [] []).
Definition rd_SH : list shent := [mkSHE 33 176 360].
Definition rd_zone (g : ectx) (pos sp1 lo hi a : Z) : Prop :=
(sp1 + 152 <= a < sp1 + 168) \/ (FA g pos + 176 + lo <= a < FA g pos + 176 + hi).

(* ================================ chunks and kept bytes ================================ *)
Lemma rd_shiftr_mod : forall x (n k : nat), (k < n)%nat ->
Z.shiftr (x mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 2 ^ 8 = Z.shiftr x (8 * Z.of_nat k) mod 2 ^ 8.
Proof.
intros x n k Hk. apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [H8|H8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
(* the bytes of a value chunk, as val_mem *)
Lemma rd_val_of_chunk : forall E (m : word -> option byte) base off (w : N) v,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w v)) ->
val_mem tfibsegs m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E v)).
Proof.
intros E m base off w v H k Hk.
destruct (H (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val YP09.cv_len]; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). rewrite Z.mod_mod by lia.
symmetry. apply rd_shiftr_mod. lia.
Qed.
Lemma rd_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
garr8 tfibsegs (mrestrict H m) a l -> garr8 tfibsegs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (cw_val_mem_kept H H' m m'); [|exact Hv].
intros x Hx. apply Hk. cbn [Z.of_nat] in Hx. lia.
Qed.

(* where a chunk at offset off of a region based on atom b sits in a state's region list *)
Fixpoint rd_cidx (cs : list YP09.chunk) (off : Z) (j : nat) : option nat :=
match cs with [] => None | ch :: cs' => if YP09.c_off ch =? off then Some j else rd_cidx cs' off (S j) end.
Fixpoint rd_ridx (rs : smem) (b : nat) (off : Z) (i : nat) : option (nat * nat) :=
match rs with
| [] => None
| r :: rs' =>
  match YP09.r_base r with
  | Some b' => if Nat.eqb b' b then
                 match rd_cidx (YP09.r_chunks r) off 0 with Some j => Some (i, j) | None => rd_ridx rs' b off (S i) end
               else rd_ridx rs' b off (S i)
  | None => rd_ridx rs' b off (S i)
  end
end.
Lemma rd_region_chunk : forall {fx : YK11.FPState} E ss ms i j r ch,
YP0l.st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> nth_error (YP09.r_chunks r) j = Some ch ->
YP09.chunk_ok tfibsegs E (ms_mem ms) (base_val E (YP09.r_base r)) ch.
Proof.
intros fx E ss ms i j r ch HS Hi Hj. pose proof (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hok & _).
rewrite Forall_forall in Hok. pose proof (Hok r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hch).
rewrite Forall_forall in Hch. exact (Hch ch (nth_error_In _ _ Hj)).
Qed.

(* an atom below the agreement bound has the base env's value *)
Lemma rd_ag : forall k E0 E n, env_agree k E0 E -> (n < k)%nat -> ew E n = ew E0 n.
Proof. intros k E0 E n H Hn. exact (proj1 H n Hn). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ the start ================================ *)
(* the state at a reader cut (pc), with the reader's k window [lo, hi) and its own atom facts AF *)
Lemma rd_start : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys AF pc lo hi cs,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
cur_at g sp1 c W2 mem2 ->
0 <= lo -> lo <= hi -> hi <= 184 ->
Forall (YP09.chunk_ok tfibsegs (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2) (FA g pos)) cs ->
forallb (chunk_inside (rd_krg lo hi cs)) cs = true ->
atoms_ok (am_env g pos c regs2 ys) AF ->
st_ok tfibsegs (am_env g pos c regs2 ys) (rd_ss pc lo hi cs AF)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom tfibsegs))) /\
sh_ok tfibsegs CW_Bx rd_SH (am_env g pos c regs2 ys) (mrestrict (w_H W2) mem2).
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c ys AF pc lo hi cs HJ Hfr HC Hcur Hlo Hlh Hhi Hcs Hcin HAF.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
unfold AM_HI in Hchi.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
set (E := am_env g pos c regs2 ys).
pose proof (am_entry B MT K XM_LIB TL LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c pc ys [] AF
  HJ Hfr HC Hcur eq_refl (Forall_nil _) I (Forall_nil _) HAF) as HS0.
fold E in HS0.
pose proof (st_ok_submem tfibsegs E (am_ss pc [] AF) _ rd_base HS0
  ltac:(cbn [am_ss am_ssb ss_mem]; unfold am_regs, am_regs0, cw_regs, rd_base; cbn [app]; submem_to)
  ltac:(vm_compute; reflexivity)) as HS1.
cbn [am_ss am_ssb ss_pc ss_regs ss_resv ss_facts] in HS1.
pose proof HC as (_ & _ & R2 & _).
assert (U2 : bv_unsigned (ew E 2) = sp1).
{ subst E. rewrite (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (U33 : bv_unsigned (ew E 33) = FA g pos).
{ subst E. rewrite (am_ew_F g pos c regs2 ys). apply unsigned_lit_small. lia. }
split.
- unfold rd_ss. apply (ast_ok_add_region tfibsegs E _ _ (rd_krg lo hi cs) HS1).
  + unfold region_wf. change (YP09.r_chunks (rd_krg lo hi cs)) with cs. rewrite Hcin. unfold rd_krg, am_frame_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
    apply andb_true_intro. split; [|reflexivity]. apply andb_true_intro. split; [reflexivity|].
    apply orb_true_intro. right. apply andb_true_intro. split; apply Z.leb_le; lia.
  + cbn [ms_mem restrict mkst].
    exact (am_frame_region_ok B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k c ys 176 360
      (176 + lo) (176 + hi) cs HJ Hfr HC ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcs).
  + cbn [ss_mem]. unfold rd_base, rd_krg, am_frame_region, stack_region, am_spill_region, am_cur_region.
    cbn [all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U2, U33. lia.
- unfold rd_SH. constructor; [|constructor].
  pose proof (am_bs_k B MT K XM_LIB g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC) as HBS.
  pose proof (sat_main_k_rd tfibsegs B LAWS ly2 S2 W2 mem2 md2 sp1 0 pos (FA g pos) LLVMF_STK (e_sp0 g)
    HAR Hin EFA Hf64 HBS ltac:(lia) ltac:(lia)) as Hcrd.
  apply (cw_shent_crd_off W2 mem2 sp1 0 E 33 (FA g pos) 176 184 Hcrd).
  + subst E. exact (am_ew_F g pos c regs2 ys).
  + lia.
  + lia.
  + subst E. exact (am_ew_SB g pos c regs2 ys).
  + lia.
Qed.

(* ================================ the zone ================================ *)
(* the frame lies in application memory, below the allocator ceiling, away from the stack *)
Lemma rd_zone_facts : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
in_app (FA g pos) 512 /\ 4096 <= FA g pos /\ FA g pos + 512 <= alloc_ceiling /\
alloc_ceiling + 32768 <= e_sp0 g /\ e_sp0 g - 320 < sp1 <= e_sp0 g - 288 /\ e_sp0 g <= 2 ^ 47 /\
0x7fff7f800000 <= alloc_ceiling.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & _).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (FS : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
rewrite EFA, FS in Happ. rewrite FS in Hfceil. rewrite FFS in Hsp0c.
split; [exact Happ|]. split; [exact Hf4096|]. split; [exact Hfceil|].
split; [exact Hsp0c|]. split; [exact Hsp|]. split; [exact Hsp047 | exact Hclo].
Qed.

Lemma rd_keep_apart : forall g pos sp1 lo hi a,
4096 <= FA g pos -> FA g pos + 512 <= alloc_ceiling ->
alloc_ceiling + 32768 <= e_sp0 g -> e_sp0 g - 320 < sp1 <= e_sp0 g - 288 ->
0 <= lo -> hi <= 184 ->
am_keepzone g pos sp1 a -> ~ rd_zone g pos sp1 lo hi a.
Proof.
intros g pos sp1 lo hi a Hf4096 Hfc Hsp0 Hsp Hlo Hhi Hz Hr.
unfold am_keepzone in Hz. unfold rd_zone in Hr. lia.
Qed.

Lemma rd_shadow_apart : forall g pos sp1 lo hi i,
in_app (FA g pos) 512 -> 4096 <= FA g pos -> FA g pos + 512 <= alloc_ceiling ->
alloc_ceiling + 32768 <= e_sp0 g -> e_sp0 g - 320 < sp1 <= e_sp0 g - 288 ->
0x7fff7f800000 <= alloc_ceiling ->
0 <= lo -> hi <= 184 -> 0 <= i < 56 ->
~ rd_zone g pos sp1 lo hi (shadow_addr (FA g pos) + i).
Proof.
intros g pos sp1 lo hi i Happ Hf4096 Hfc Hsp0 Hsp Hclo Hlo Hhi Hi Hr.
unfold rd_zone, shadow_addr, SHADOW_OFF in Hr.
pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
lia.
Qed.

(* ================================ the end ================================ *)
(* RUN 0x820d0: the executor state of a reader's last run, with the zone it wrote, the cursor and the record
   it left, is the cut inv_run *)
Lemma rd_exit : forall g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 c' k' od,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 35 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = PC_RUN -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
0 <= lo -> hi <= 184 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a -> aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
cur_at g sp1 c' W2 (ms_mem ms) -> k_at g pos k' W2 (ms_mem ms) -> enc_okZ k' od ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 c' k' od
  HJ Hfr Hk Hmo HC Hops HJ3 HAG HS Hpc Hresv Hkeep H26 Hlo Hhi KE Hcur' Hkat' Henc.
apply SRr_ret.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
rewrite Hpc in Ems.
destruct (rd_zone_facts g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (Happ & Hf4096 & Hfc & Hsp0 & Hsp & Hsp47 & Hclo).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    k (Z_to_bv 64 PC_RUN) ss E HC HJ3 HAG HS' Hkeep).
  - intros a Ha. apply KE.
    + unfold am_keepzone in Ha. lia.
    + exact (rd_keep_apart g pos sp1 lo hi a Hf4096 Hfc Hsp0 Hsp Hlo Hhi Ha).
  - intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
    + exact (rd_shadow_apart g pos sp1 lo hi i Happ Hf4096 Hfc Hsp0 Hsp Hclo Hlo Hhi Hi).
  - pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm. }
rewrite Ems. change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 PC_RUN) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs PC_RUN (ms_regs ms) (ms_mem ms) md3).
unfold inv_run.
apply (am_mcut B MT K XM_LIB g pos sp1 0 PC_RUN _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k HJ3 Hfr Hk Hmo HC3).
cbv beta. split.
- destruct Hops as (Hops & R26). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 26%bv HS), H26.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
- exists c', k', od. split; [exact Hcur'|]. split; [exact Hkat' | exact Henc].
Qed.

(* the record at the end: the fields the reader stores, the rest kept from the cut's k_rdZ *)
Lemma rd_kat : forall g pos W2 mem2 mem3 kind pv dv a b c d bytes,
k_at g pos (k_rdZ kind pv dv) W2 mem2 ->
(forall x, FA g pos + 176 <= x < FA g pos + 360 -> ~ (FA g pos + 200 <= x < FA g pos + 240) ->
 aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x) ->
0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= c < 2 ^ 32 -> - 2 ^ 31 <= d < 2 ^ 31 -> length bytes = 24%nat ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 24) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 28) 4 b ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 32) 4 c ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 36) 4 d ->
garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + 40) bytes ->
k_at g pos (rdk kind pv dv a b c d bytes) W2 mem3.
Proof.
intros g pos W2 mem2 mem3 kind pv dv a b c d bytes (Hk & Hwf) KE Ha Hb Hc Hd Hl Va Vb Vc Vd Vy.
unfold k_at.
set (q := FA g pos + 176) in *.
assert (VK : forall o n v, 0 <= o -> o + Z.of_nat n <= 184 -> (o + Z.of_nat n <= 24 \/ 64 <= o) ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (q + o) n v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) (q + o) n v).
{ intros o n v Ho Hn Hw Hv. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
  intros x Hx. apply KE; subst q; lia. }
assert (GK : forall o l, 64 <= o -> o + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (mrestrict (w_H W2) mem2) (q + o) l -> garr8 tfibsegs (mrestrict (w_H W2) mem3) (q + o) l).
{ intros o l Ho Hn Hg. apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hg].
  intros x Hx. apply KE; subst q; lia. }
destruct Hk as (Vkind & Vp & Vdesk & _ & _ & _ & _ & _ & Vn & Vrc & Vbef & Vout & Vwrc & Vwant & Vwl & Vwk & Vwd).
destruct Hwf as (Wk & Wp & Wd & _ & _ & _ & _ & Wn & Wrc & Wwrc & Wwl & Wwk & Wwd & _ & Wbef & Wout & Wwant).
cbn [kz_kind kz_p kz_desk kz_n kz_rc kz_before kz_out kz_want_rc kz_want kz_want_len kz_want_key kz_want_display
  k_rdZ] in *.
split.
- unfold kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display rdk].
  split; [rewrite <- (Z.add_0_r q); apply (VK 0 4%nat); [lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vkind]|].
  split; [apply (VK 8 8%nat); [lia | cbn; lia | cbn; lia | exact Vp]|].
  split; [apply (VK 16 8%nat); [lia | cbn; lia | cbn; lia | exact Vdesk]|].
  split; [exact Va|]. split; [exact Vb|]. split; [exact Vc|]. split; [exact Vd|]. split; [exact Vy|].
  split; [apply (VK 64 8%nat); [lia | cbn; lia | cbn; lia | exact Vn]|].
  split; [apply (VK 72 4%nat); [lia | cbn; lia | cbn; lia | exact Vrc]|].
  split; [apply (GK 76); [lia | unfold fa5; rewrite repeat_length; cbn; lia | exact Vbef]|].
  split; [apply (GK 108); [lia | unfold fa5; rewrite repeat_length; cbn; lia | exact Vout]|].
  split; [apply (VK 140 4%nat); [lia | cbn; lia | cbn; lia | exact Vwrc]|].
  split; [apply (GK 144); [lia | rewrite repeat_length; cbn; lia | exact Vwant]|].
  split; [apply (VK 168 8%nat); [lia | cbn; lia | cbn; lia | exact Vwl]|].
  split; [apply (VK 176 4%nat); [lia | cbn; lia | cbn; lia | exact Vwk]|].
  apply (VK 180 4%nat); [lia | cbn; lia | cbn; lia | exact Vwd].
- unfold kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display rdk].
  repeat split; try lia; try exact Hl; try exact Wbef; try exact Wout; try exact Wwant.
Qed.

(* the cursor at the end, from the cursor region's two chunks *)
Lemma rd_cur : forall g sp1 c j W3 mem3 E,
YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem3) sp1 (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) mem3) sp1 (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
ew E 35 = Z_to_bv 64 (e_p g + c) -> ew E 36 = Z_to_bv 64 (e_n g - c) ->
0 <= c -> 0 <= j -> c + j <= e_n g -> 0 <= e_p g -> e_p g + e_n g < 2 ^ 64 ->
cur_at g sp1 (c + j) W3 mem3.
Proof.
intros g sp1 c j W3 mem3 E H152 H160 E35 E36 Hc Hj Hcj Hp Hpn.
pose proof (rd_val_of_chunk E _ sp1 152 8 (SOff 35 j) H152) as V1.
pose proof (rd_val_of_chunk E _ sp1 160 8 (SOff 36 (- j)) H160) as V2.
cbn [sv_denot] in V1, V2. rewrite E35 in V1. rewrite E36 in V2.
rewrite (unsigned_lit_small (e_p g + c)) in V1 by lia. rewrite (unsigned_lit_small (e_p g + c + j)) in V1 by lia.
rewrite (unsigned_lit_small (e_n g - c)) in V2 by lia. rewrite (unsigned_lit_small (e_n g - c + - j)) in V2 by lia.
split; [lia|]. split.
- replace (e_p g + (c + j)) with (e_p g + c + j) by lia. exact V1.
- replace (e_n g - (c + j)) with (e_n g - c + - j) by lia. exact V2.
Qed.
(* the end of a reader of any kind at RUN from the final state's facts: the cursor's two chunks (c + j bytes taken), the
   kept fact over rd_zone, and the record's fields a / b / c / delta / bytes as the final memory holds them *)
Lemma rd_endk : forall g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k kind pv dv od Ef ssf msf md3 j
  a b cc d bytes,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
0 <= kind <= 11 -> pd_okA pv dv od -> k_at g pos (k_rdZ kind pv dv) W2 mem2 -> 0 <= c ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem msf) md3 k ->
env_agree 41 (am_env g pos c regs2 ys) Ef ->
YP0l.st_ok tfibsegs Ef ssf (restrict (w_H W2) msf) -> ss_pc ssf = PC_RUN -> ss_resv ssf = None ->
am_keep_ok (ss_regs ssf) = true -> sr_get (ss_regs ssf) 26%bv = SOff 26 0 ->
24 <= lo -> hi <= 64 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) (ms_mem msf) a = aview tfibsegs (w_H W2) mem2 a) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem msf)) (bv_unsigned (ew Ef 2)) (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem msf)) (bv_unsigned (ew Ef 2)) (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
0 <= j -> c + j <= e_n g ->
reader_ok kind a b cc d bytes 0 ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (FA g pos + 176 + 24) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (FA g pos + 176 + 28) 4 b ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (FA g pos + 176 + 32) 4 cc ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (FA g pos + 176 + 36) 4 d ->
garr8 tfibsegs (mrestrict (w_H W2) (ms_mem msf)) (FA g pos + 176 + 40) bytes ->
SRr tfibsegs W2 {| cfg_ms := msf; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k kind pv dv od Ef ssf msf md3 j a b cc d bytes
  HJ Hfr Hk Hmo HC Hops Hkind Hpd Hkat Hc0 HJ3 HAE HS Hpc Hresv Hkeep H26 Hlo Hhi KE HC1 HC2 Hj Hcj Hrd Va Vb Vc Vd Vy.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
unfold AM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
assert (FB : fs_frame_bytes 3 = 512) by (vm_compute; reflexivity). rewrite FB in Hfceil.
pose proof HC as (_ & _ & R2 & _).
assert (X2 : bv_unsigned (ew Ef 2) = sp1).
{ rewrite (rd_ag 41 _ Ef 2 HAE ltac:(lia)), (am_ew_reg g pos c regs2 ys 2 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite X2 in HC1, HC2.
pose proof Hrd as (Ha & Hb & Hc & Hd & Hl & _).
apply (rd_exit g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k Ef ssf msf md3 (c + j)
  (rdk kind pv dv a b cc d bytes) od HJ Hfr Hk Hmo HC Hops HJ3
  ltac:(eapply env_agree_le; [|exact HAE]; lia) HS Hpc Hresv Hkeep H26 ltac:(lia) ltac:(lia) KE).
- apply (rd_cur g sp1 c j W2 _ Ef HC1 HC2).
  + rewrite (rd_ag 41 _ Ef 35 HAE ltac:(lia)). apply am_ew_CP.
  + rewrite (rd_ag 41 _ Ef 36 HAE ltac:(lia)). apply am_ew_CN.
  + exact Hc0.
  + exact Hj.
  + exact Hcj.
  + lia.
  + lia.
- apply (rd_kat g pos W2 mem2 _ kind pv dv a b cc d bytes Hkat); [| lia | lia | lia | lia | exact Hl | exact Va | exact Vb
    | exact Vc | exact Vd | exact Vy].
  intros x Hx1 Hx2. apply KE; [lia | unfold rd_zone; lia].
- apply rd_enc_ok; [exact Hkind | exact Hpd | exact Hrd].
Qed.

(* a field of the cut's record outside the reader's window, kept *)
Lemma rd_vm_kept : forall g pos sp1 lo hi (W2 : world tfibsegs) mem2 mem3 o n v,
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
4096 <= FA g pos -> FA g pos + 512 <= sp1 -> sp1 <= 2 ^ 47 -> 0 <= o -> o + Z.of_nat n <= 184 ->
(o + Z.of_nat n <= lo \/ hi <= o) ->
val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) n v ->
val_mem tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + o) n v.
Proof.
intros g pos sp1 lo hi W2 mem2 mem3 o n v KE HF HFs H47 Ho Hn Hw Hv.
apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
intros x Hx. apply KE; [lia | unfold rd_zone; lia].
Qed.
Lemma rd_garr8_kept_k : forall g pos sp1 lo hi (W2 : world tfibsegs) mem2 mem3 o l,
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
4096 <= FA g pos -> FA g pos + 512 <= sp1 -> sp1 <= 2 ^ 47 -> 0 <= o -> o + Z.of_nat (length l) <= 184 ->
(o + Z.of_nat (length l) <= lo \/ hi <= o) ->
garr8 tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) l ->
garr8 tfibsegs (mrestrict (w_H W2) mem3) (FA g pos + 176 + o) l.
Proof.
intros g pos sp1 lo hi W2 mem2 mem3 o l KE HF HFs H47 Ho Hn Hw Hv.
apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
intros x Hx. apply KE; [lia | unfold rd_zone; lia].
Qed.
End b.
End a.

(* ================================ the tactics ================================ *)
(* The walk keeps HAE : env_agree 41 E0 E for its current env E (E0 = am_env g pos c regs2 ys; the byte atoms
   37 .. 40 are below every run's fresh atoms) and the base facts X2 : bv_unsigned (ew E0 2) = sp1,
   X33 : bv_unsigned (ew E0 33) = FA g pos, EFA : frame_addr ly2 3 pos = FA g pos. *)
(* after a run or a branch: carry HAE to the env of the newest state *)
Ltac rd_refresh :=
lazymatch goal with HS : YP0l.st_ok _ ?E' _ _, HAE : env_agree ?k ?E0 ?E |- _ =>
tryif constr_eq E E' then idtac
else (let H := fresh "HAE" in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE)
end.
(* ew E n of the current env as the base env's *)
Ltac rd_ew E n :=
lazymatch goal with HAE : env_agree ?k ?E0 E |- _ => tryif constr_eq E E0 then idtac else rewrite (rd_ag k E0 E n HAE ltac:(lia)) end.
(* the write windows of a reader's state: the cursor (atom 2 = sp1, in the caller's stack allowance) and the
   k window (atom 33 = F, inside the entry's own frame (3, pos)) *)
Ltac rd_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
lazymatch goal with HAE : env_agree _ ?E0 E |- _ =>
lazymatch goal with X2 : bv_unsigned (ew E0 2) = ?spv, X33 : bv_unsigned (ew E0 33) = ?Fv |- _ =>
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rd_ew E 2%nat; rewrite X2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
  [reflexivity | rd_ew E 33%nat; exact X33 |
   let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
   right; right; right; exists 3; eexists; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
   lazymatch goal with EF : frame_addr _ 3 _ = Fv |- _ => rewrite EF end;
   change (fs_frame_bytes 3) with 512; lia
  |] ]
end end end.
(* the zone of a run's write windows is rd_zone *)
Ltac rd_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; unfold rd_zone;
   first [ lia
         | lazymatch type of Hb with context [ew ?E 2%nat] =>
             lazymatch goal with HAE : env_agree ?k ?E0 E, X2 : bv_unsigned (ew ?E0 2) = _ |- _ =>
               (tryif constr_eq E E0 then idtac else rewrite (rd_ag k E0 E 2%nat HAE ltac:(lia)) in Hb); rewrite X2 in Hb end end; lia
         | lazymatch type of Hb with context [ew ?E 33%nat] =>
             lazymatch goal with HAE : env_agree ?k ?E0 E, X33 : bv_unsigned (ew ?E0 33) = _ |- _ =>
               (tryif constr_eq E E0 then idtac else rewrite (rd_ag k E0 E 33%nat HAE ltac:(lia)) in Hb); rewrite X33 in Hb end end; lia ] | ]);
destruct Hr.
(* the chunk at offset off of the region on atom b in the state of HS, as H *)
Ltac rd_chunk HS b off H :=
lazymatch type of HS with YP0l.st_ok ?segs ?E ?ss ?ms =>
let p := eval vm_compute in (rd_ridx (ss_mem ss) b off 0) in
lazymatch p with Some (?i, ?j) =>
let r := eval vm_compute in (nth i (ss_mem ss) (stack_region 0)) in
let ch := eval vm_compute in (nth j (YP09.r_chunks r) (YP09.mkChunk 0 (CZero 0))) in
pose proof (rd_region_chunk E ss ms i j r ch HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H;
cbn [YP09.r_base base_val ms_mem restrict] in H
end end.
