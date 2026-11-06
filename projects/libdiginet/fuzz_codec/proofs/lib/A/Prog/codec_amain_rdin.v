(* The input-byte read of the reader segments of the image-A walk of LLVMFuzzerTestOneInput (fuzz_u8 inlined:
   `ld p,152(s1); ...; lb t,(p >> 3)+SB; beqz t,FAST; j SLOW; FAST: lbu b,0(p)`), on top of the extended token
   engine of lib/A/Prog/CPgTokJ.v and the reader state of lib/A/Prog/codec_amain_rdlib.v.
   - rd_ib g i: input byte i (0 past the end), with its range (rd_ib_range).
   - rd_in_val: at every state the journal from the entry reaches, input byte i < n holds rd_ib g i (the journal's
     footprint is empty, so clause F2 keeps the block's bytes).
   - rd_inr j: the read-only 1-byte region at the cursor atom 35 offset j whose chunk is the atom AM_X0 + j; a reader
     adds it after the in.n test (rd_inr_ok: its region_ok when the atom holds rd_ib g (c + j) and c + j < n).
   - rd_in_obl: the engine's obligation of the check, mkOB (SOff 35 j) 1, from the block's shadow (obl_of_block on
     the journal's AR).
   - tactics rd_in_add (add rd_inr j to the state) and rd_obl (close an obligation). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st CPgTokJ codec_amain_rdlib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_owe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* input byte i of the entry state *)
Definition rd_ib (g : ectx) (i : Z) : Z := nth (Z.to_nat i) (map (fun b : byte => bv_unsigned b) (e_pl g)) 0.
Lemma rd_ib_range : forall g i, 0 <= rd_ib g i < 256.
Proof.
intros g i. unfold rd_ib.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length (map (fun b : byte => bv_unsigned b) (e_pl g)))) as [Hl|Hl].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hl.
  rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) (e_pl g) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
- rewrite nth_overflow by exact Hl. lia.
Qed.
(* the read-only 1-byte region of input byte j past the cursor *)
Definition rd_inr (j : nat) : YP09.region :=
YP09.mkRegion (Some 35%nat) (Z.of_nat j) (Z.of_nat j + 1) 0 0 [YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (AM_X0 + j) 0))].
(* a reader's own atoms: input bytes c .. c + nb - 1 at AM_X0 .., each in [0, 255] *)
Definition rd_ys (g : ectx) (c : Z) (nb : nat) : list Z := map (fun j => rd_ib g (c + Z.of_nat j)) (seq 0 nb).
Definition rd_AF (nb : nat) : list (nat * afact) := map (fun j => ((AM_X0 + j)%nat, mkAF 0 255 0)) (seq 0 nb).
Lemma rd_EY : forall g pos c regs nb j, (j < nb)%nat ->
ew (am_env g pos c regs (rd_ys g c nb)) (AM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)).
Proof.
assert (NM : forall (f : nat -> Z) nb j, (j < nb)%nat -> nth j (map f (seq 0 nb)) 0 = f j).
{ intros f nb j Hj. rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
  rewrite map_nth, seq_nth by exact Hj. reflexivity. }
intros g pos c regs nb j Hj. rewrite am_ew_y. unfold rd_ys.
rewrite (NM (fun j0 : nat => rd_ib g (c + Z.of_nat j0)) nb j Hj). reflexivity.
Qed.
Lemma rd_AF_ok : forall g pos c regs nb, atoms_ok (am_env g pos c regs (rd_ys g c nb)) (rd_AF nb).
Proof.
intros g pos c regs nb. unfold rd_AF.
assert (H : forall l, (forall j, In j l -> (j < nb)%nat) ->
  atoms_ok (am_env g pos c regs (rd_ys g c nb)) (map (fun j => ((AM_X0 + j)%nat, mkAF 0 255 0)) l)).
{ induction l as [|j l IH]; intros Hl; cbn [map atoms_ok]; [exact I|]. split.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (rd_EY g pos c regs nb j (Hl j (or_introl eq_refl))).
    pose proof (rd_ib_range g (c + Z.of_nat j)). rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
  - apply IH. intros j' Hj'. apply Hl. right. exact Hj'. }
apply H. intros j Hj. apply in_seq in Hj. lia.
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.

Lemma rd_in_val : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k (m : word -> option byte) md' k' i,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 m md' k' ->
0 <= i < e_n g ->
val_mem tfibsegs (mrestrict (w_H W2) m) (e_p g + i) 1 (rd_ib g i).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k m md' k' i HJ Hfr HC HJm Hi.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & _ & _ & Hblk).
destruct (Hblk ltac:(lia)) as (Hin2 & Hin0).
pose proof HC as HG. do 44 (destruct HG as (_ & HG)). destruct HG as (HG & _).
pose proof HC as (Hpre & _). unfold e_pre, codec_lib_pre_x in Hpre.
destruct Hpre as (_ & _ & _ & _ & _ & Hnpl & _).
assert (Hlen : (Z.to_nat i < length (map (fun b : byte => bv_unsigned b) (e_pl g)))%nat).
{ rewrite length_map. lia. }
destruct (HG (Z.to_nat i) Hlen) as (Hv & _).
rewrite Z2Nat.id in Hv by lia.
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 m); [|exact Hv].
intros x Hx. cbn [Z.of_nat] in Hx. replace x with (e_p g + i) by lia.
pose proof HJm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2m & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2m (e_p g) (e_n g) i Hin0 Hin2 ltac:(lia) (inFP_nil _)).
rewrite (F2 (e_p g) (e_n g) i Hin0 Hin2 ltac:(lia) (inFP_nil _)). reflexivity.
Qed.

Lemma rd_inr_ok : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k (m : word -> option byte) md' k' c (j : nat) E,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 m md' k' ->
0 <= c -> c + Z.of_nat j < e_n g ->
ew E 35 = Z_to_bv 64 (e_p g + c) -> ew E (AM_X0 + j) = Z_to_bv 64 (rd_ib g (c + Z.of_nat j)) ->
region_ok tfibsegs E (mrestrict (w_H W2) m) (rd_inr j).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k m md' k' c j E HJ Hfr HC HJm Hc Hcj E35 EY.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & Hp & Hpn & _).
unfold AM_HI in Hpn.
pose proof (rd_ib_range g (c + Z.of_nat j)) as Hr.
unfold region_ok, rd_inr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E35, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs E _ (e_p g + c) (Z.of_nat j) 1 (SOff (AM_X0 + j) 0) (rd_ib g (c + Z.of_nat j))).
- cbn [sv_denot]. rewrite EY, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
- lia.
- change (N.to_nat 1) with 1%nat. replace (e_p g + c + Z.of_nat j) with (e_p g + (c + Z.of_nat j)) by lia.
  exact (rd_in_val g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k m md' k' (c + Z.of_nat j) HJ Hfr HC HJm ltac:(lia)).
Qed.

Lemma rd_in_obl : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k (m : word -> option byte) md' k' c j E,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 m md' k' ->
0 <= c -> 0 <= j -> c + j < e_n g ->
ew E 35 = Z_to_bv 64 (e_p g + c) -> ew E 32 = Z_to_bv 64 SB ->
range_addressable (YCbn.rd_of tfibsegs (mrestrict (w_H W2) m)) (U E CW_Bx) (U E (SOff 35 j)) 1.
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k m md' k' c j E HJ Hfr HC HJm Hc Hj Hcj E35 E32.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & Hp & Hpn & Hblk).
unfold AM_HI in Hpn.
destruct (Hblk ltac:(lia)) as (Hin2 & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
rewrite (cw_U_offx E 35 (e_p g + c) j E35 ltac:(lia)), Z.mod_small by lia.
apply (obl_of_block tfibsegs B LAWS ly2 S2 W2 m md' E CW_Bx (e_p g + c + j) 1 (e_p g) (e_n g) (proj1 HJm) Hin2).
- exact (cw_U_Bx E E32).
- lia.
- lia.
Qed.

(* ================================ the end of a reader of kinds 0 .. 4 ================================ *)
(* An unwritten scalar field of k (a, b, c, delta at 24, 28, 32, 36) still holds the 0 HEAD stored. *)
Lemma rd_kept4 : forall g pos sp1 W2 mem2 (m : word -> option byte) kind pv dv lo hi o,
k_at g pos (k_rdZ kind pv dv) W2 mem2 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi x -> aview tfibsegs (w_H W2) m x = aview tfibsegs (w_H W2) mem2 x) ->
4096 <= FA g pos -> FA g pos + 512 <= 2 ^ 47 -> FA g pos + 360 <= sp1 ->
(o = 24 \/ o = 28 \/ o = 32 \/ o = 36) -> (o + 4 <= lo \/ hi <= o) ->
val_mem tfibsegs (mrestrict (w_H W2) m) (FA g pos + 176 + o) 4 0.
Proof.
intros g pos sp1 W2 mem2 m kind pv dv lo hi o ((_ & _ & _ & Va & Vb & Vc & Vd & _) & _) KE HF HF2 Hsp Ho Hw.
cbn [kz_a kz_b kz_c kz_delta k_rdZ] in Va, Vb, Vc, Vd.
assert (V : val_mem tfibsegs (mrestrict (w_H W2) mem2) (FA g pos + 176 + o) 4 0)
  by (destruct Ho as [-> | [-> | [-> | ->]]]; assumption).
apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 m); [|exact V].
intros x Hx. cbn [Z.of_nat] in Hx. apply KE; [lia|]. unfold rd_zone. lia.
Qed.
(* a value chunk of four bytes, as the field's u32 / int32 value *)
Definition s32 (x : Z) : Z := if x mod 2 ^ 32 <? 2 ^ 31 then x mod 2 ^ 32 else x mod 2 ^ 32 - 2 ^ 32.
Lemma s32_range : forall x, - 2 ^ 31 <= s32 x < 2 ^ 31.
Proof.
intros x. unfold s32. pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)).
destruct (Z.ltb_spec (x mod 2 ^ 32) (2 ^ 31)); lia.
Qed.
Lemma rd_val_congr : forall (m : word -> option byte) a n x y,
x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) -> val_mem tfibsegs m a n x -> val_mem tfibsegs m a n y.
Proof. intros m a n x y Hxy H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Hxy. reflexivity. Qed.
Lemma rd_chunk_u32 : forall E (m : word -> option byte) base off v,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 4 v)) ->
val_mem tfibsegs m (base + off) 4 (bv_unsigned (sv_denot E v) mod 2 ^ 32).
Proof.
intros E m base off v H. apply (rd_val_congr m _ 4 (bv_unsigned (sv_denot E v))); [change (8 * Z.of_nat 4) with 32; rewrite Z.mod_mod by lia; reflexivity|].
exact (rd_val_of_chunk E m base off 4 v H).
Qed.
Lemma rd_chunk_s32 : forall E (m : word -> option byte) base off v,
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 4 v)) ->
val_mem tfibsegs m (base + off) 4 (s32 (bv_unsigned (sv_denot E v))).
Proof.
intros E m base off v H. apply (rd_val_congr m _ 4 (bv_unsigned (sv_denot E v))); [|exact (rd_val_of_chunk E m base off 4 v H)].
change (8 * Z.of_nat 4) with 32. unfold s32. set (x := bv_unsigned (sv_denot E v)).
destruct (x mod 2 ^ 32 <? 2 ^ 31); [rewrite Z.mod_mod by lia; reflexivity|].
replace (x mod 2 ^ 32 - 2 ^ 32) with (x mod 2 ^ 32 + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_mod by lia. reflexivity.
Qed.
Lemma rd_u32_range : forall x, 0 <= x mod 2 ^ 32 < 2 ^ 32.
Proof. intros x. apply Z.mod_pos_bound. lia. Qed.

(* RUN 0x820d0 for a reader of kind 0 .. 4: the final state, its journal, the kept fact over the reader's zone, the
   cursor's two chunks (j bytes taken) and the four scalar fields' values give the cut inv_run *)
Lemma rd_end : forall g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kind pv dv od lo hi Ef ss ms md3 j a b cc d,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
k_at g pos (k_rdZ kind pv dv) W2 mem2 -> pd_okA pv dv od -> 0 <= kind <= 4 -> 0 <= c ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 41 (am_env g pos c regs2 ys) Ef ->
st_ok tfibsegs Ef ss (restrict (w_H W2) ms) -> ss_pc ss = PC_RUN -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
24 <= lo -> hi <= 40 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi x -> aview tfibsegs (w_H W2) (ms_mem ms) x = aview tfibsegs (w_H W2) mem2 x) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs Ef (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
0 <= j -> c + j <= e_n g ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 176 + 24) 4 a ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 176 + 28) 4 b ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 176 + 32) 4 cc ->
val_mem tfibsegs (mrestrict (w_H W2) (ms_mem ms)) (FA g pos + 176 + 36) 4 d ->
0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= cc < 2 ^ 32 -> - 2 ^ 31 <= d < 2 ^ 31 ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (inv_run B MT K XM_LIB g pos sp1 ops).
Proof.
intros g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kind pv dv od lo hi Ef ss ms md3 j a b cc d
  HJ Hfr Hk Hmo HC Hops Hkat Hpd Hkind Hc HJ3 HAG HS Hpc Hresv Hkeep H26 Hlo Hhi KE Ca Cb Hj Hcj Va Vb Vc Vd Ha Hb Hcc Hd.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & Hf4096 & Hfceil & FS3 & Hchi & Hclo & _ & Hsp & Hsp0c & Hsp047 & _ & _ & Hng & Hp & Hpn & _).
unfold AM_HI in Hchi, Hpn.
assert (FFS : LLVMF_STK = 32768) by reflexivity.
change (fs_frame_bytes 3) with 512 in Hfceil.
destruct HAG as (HA & HD).
assert (E35 : ew Ef 35 = Z_to_bv 64 (e_p g + c)) by (rewrite (HA 35%nat ltac:(lia)); exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew Ef 36 = Z_to_bv 64 (e_n g - c)) by (rewrite (HA 36%nat ltac:(lia)); exact (am_ew_CN g pos c regs2 ys)).
apply (rd_exit B MT K XM_LIB LAWS g pos sp1 ops lo hi c ys ly2 S2 W2 regs2 mem2 md2 k Ef ss ms md3 (c + j)
  (rdk kind pv dv a b cc d (repeat 0 24)) od HJ Hfr Hk Hmo HC Hops HJ3).
- split; [intros i Hi; apply HA; lia | exact HD].
- exact HS.
- exact Hpc.
- exact Hresv.
- exact Hkeep.
- exact H26.
- lia.
- lia.
- exact KE.
- exact (rd_cur g sp1 c j W2 (ms_mem ms) Ef Ca Cb E35 E36 Hc Hj Hcj ltac:(lia) ltac:(lia)).
- apply (rd_kat g pos W2 mem2 (ms_mem ms) kind pv dv a b cc d (repeat 0 24) Hkat).
  + intros x Hx Hw. apply KE; [lia|]. unfold rd_zone. lia.
  + exact Ha.
  + exact Hb.
  + exact Hcc.
  + exact Hd.
  + apply repeat_length.
  + exact Va.
  + exact Vb.
  + exact Vc.
  + exact Vd.
  + destruct Hkat as ((_ & _ & _ & _ & _ & _ & _ & Vy & _) & _). cbn [kz_bytes k_rdZ] in Vy.
    apply (rd_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem ms)); [|exact Vy].
    intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat] in Hx. apply KE; [lia|]. unfold rd_zone. lia.
- apply rd_enc_ok; [lia | exact Hpd |].
  unfold codec_owe.reader_ok. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply repeat_length|]. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia|].
  split; [lia|]. split; [intros; lia|]. split; intros; lia.
Qed.

(* the input block lies below the allocator ceiling and away from the entry's frame *)
Lemma rd_in_sep : forall g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 ->
0 < e_n g -> e_p g + e_n g <= alloc_ceiling /\ (e_p g + e_n g <= FA g pos \/ FA g pos + 512 <= e_p g).
Proof.
intros g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC Hn.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (EFA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
destruct (Hblk Hn) as (Hin2 & _).
pose proof HJ as (HAR & _).
assert (Hin3 : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 3 pos HAR Hin2 Hin3) as Hd.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR Hin2) as (_ & _ & Hbc & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
split; lia.
Qed.
End b.
End a.

(* Close the obligation `range_addressable (rd_of ..) (U Ev CW_Bx) (U Ev (SOff 35 j)) 1` of a run whose start env Ev is
   the walk's base env E0 extended by ewset (the token atoms): HJ0 / HFR / HC0 the cut's journal, frames and
   mcommon, HJm the run's journal, E35 / E32 the base env's atoms 35 and 32. *)
Ltac rd_obl LAWS HJ0 HFR HC0 c E35 E32 :=
lazymatch goal with
| HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- range_addressable _ (U ?Ev CW_Bx) (U ?Ev (SOff 35 ?j)) 1 =>
  eapply (rd_in_obl _ _ _ _ LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ c j Ev HJ0 HFR HC0 HJm);
  [ lia | lia | lia
  | rewrite ?ew_ewset_other by lia; exact E35
  | rewrite ?ew_ewset_other by lia; exact E32 ]
end.
(* Add the region rd_inr j to the state HS (at the read of input byte j): its region_ok by rd_inr_ok, its
   disjointness from the state's regions by their extents (B2 / B33 / E35 the base env's atoms 2, 33, 35; EY the
   atom AM_X0 + j). *)
Ltac rd_in_add LAWS HJ0 HFR HC0 c j E35 EYall HSEP :=
lazymatch goal with
| HS : st_ok _ ?Ev ?ssv ?msv, HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let HS1 := fresh "HS" in
  pose proof (ast_ok_add_region tfibsegs Ev ssv msv (rd_inr j) HS eq_refl) as HS1;
  specialize (HS1 ltac:(cbn [ms_mem restrict];
    eapply (rd_inr_ok _ _ _ _ LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ c j Ev HJ0 HFR HC0 HJm);
    [ lia | cbn [Z.of_nat]; lia
    | rewrite ?ew_ewset_other by lia; exact E35
    | unfold AM_X0; rewrite ?ew_ewset_other by lia; apply EYall; lia ]));
  specialize (HS1 ltac:(
    lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
      let rs2 := eval vm_compute in rsy in let ry2 := eval vm_compute in ry in change (all_disjoint Ey ry2 rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_nat];
    rewrite ?ew_ewset_other by lia;
    repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H end;
    rewrite ?E35, ?unsigned_lit_small by lia;
    let S1 := fresh "S1" in let S2 := fresh "S2" in destruct (HSEP ltac:(lia)) as [S1 S2];
    repeat split; lia));
  clear HS; rename HS1 into HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS
end.
(* The write windows of a reader's state on the run's start env Ev (the base env E0 extended by ewset): the
   cursor (atom 2 = sp1) in the caller's stack allowance, the k window (atom 33 = F) in the own frame (3, pos).
   B2 / B33: the base env's atoms 2 and 33; EF : frame_addr ly2 3 pos = F. *)
Ltac rdj_awr B2 B33 EF :=
idtac; lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0 fp b0 bc ly own);
lazymatch type of B2 with bv_unsigned (ew _ 2) = ?spv =>
lazymatch type of B33 with bv_unsigned (ew _ 33) = ?Fv =>
let C2 := fresh "C2" in let C33 := fresh "C33" in
assert (C2 : bv_unsigned (ew Ev 2) = spv) by (rewrite ?ew_ewset_other by lia; exact B2);
assert (C33 : bv_unsigned (ew Ev 33) = Fv) by (rewrite ?ew_ewset_other by lia; exact B33);
repeat first
[ apply YCbq.awr_ok_nil
| apply YCbq.awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| eapply (YCbq.awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
  [reflexivity | rewrite C2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
| eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat Fv);
  [reflexivity | exact C33 |
   let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
   right; right; right; eexists; eexists; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
   rewrite EF; change (fs_frame_bytes 3) with 512; lia
  |] ];
clear C2 C33
end end end.
(* the zone of those windows is rd_zone *)
Ltac rdj_kwr B2 B33 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?ew_ewset_other in Hb by lia;
   rewrite ?B2, ?B33 in Hb; unfold rd_zone; lia | ]);
destruct Hr.

(* ================================ a whole reader, by exploration ================================ *)
(* the offset j of the cursor chunk at 152(sp1) of a state's region list: j bytes taken *)
Fixpoint rd_cur_off (rs : smem) : option Z :=
match rs with
| [] => None
| r :: rs' =>
  match YP09.r_base r with
  | Some 2%nat =>
    match find (fun ch => YP09.c_off ch =? 152) (YP09.r_chunks r) with
    | Some ch => match YP09.c_val ch with CVal _ (SOff 35%nat j) => Some j | _ => rd_cur_off rs' end
    | None => rd_cur_off rs'
    end
  | _ => rd_cur_off rs'
  end
end.
(* a branch on in.n - j (the atom 36 at offset -j), as a fact over Z *)
Ltac rd_brn Hb E36 :=
rewrite ?branch_eq_U, ?branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb].
(* the run to the next stop (an undecided test of in.n, or RUN 0x820d0), its input-byte obligations closed *)
Ltac rd_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA :=
cwj_run_to ltac:(rdj_awr B2 B33 EFA) 532688; try (rd_obl LAWS HJ0 HFR HC c E35 E32).
(* Every path of a reader from its cut: run; at RUN finish with fin; at a test of in.n split it, and on the
   in.n <> 0 side put the next input byte's region (j = the bytes taken, read off the cursor chunk) first. *)
Ltac rd_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin :=
rd_run_t LAWS HJ0 HFR HC c E35 E32 B2 B33 EFA; cw_keep ltac:(rdj_kwr B2 B33);
lazymatch goal with
| HS : st_ok _ _ ?ss _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with
  | 532688 => fin
  | _ =>
    let Hb := fresh "Hb" in
    cw_branch Hb; rd_brn Hb E36;
    [ rd_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
    | lazymatch goal with HS' : st_ok _ _ ?ss' _ |- _ =>
        let jz := eval vm_compute in (rd_cur_off (ss_mem ss')) in
        lazymatch jz with Some ?jj =>
          let j := eval vm_compute in (Z.to_nat jj) in
          rd_in_add LAWS HJ0 HFR HC c j E35 EYall HSEP;
          rd_explore LAWS HJ0 HFR HC c E35 E32 E36 B2 B33 EFA EYall HSEP fin
        end
      end ]
  end
end.
(* the four scalar fields of k at RUN: kept (outside the window) or the chunk at 176 + o *)
Ltac rd_field Hkat KE :=
lazymatch goal with
| HS : st_ok _ ?Ef _ _ |- val_mem _ _ (?F + 176 + ?o) 4 _ =>
  first
  [ eapply rd_kept4; [exact Hkat | exact KE | lia | lia | lia | lia | lia]
  | let C := fresh "C" in let off := eval vm_compute in (176 + o) in
    rd_chunk HS 33%nat off C; rewrite ?ew_ewset_other in C by lia;
    lazymatch goal with B33 : bv_unsigned (ew _ 33) = F |- _ => rewrite B33 in C end;
    replace (F + 176 + o) with (F + off) by lia;
    first [ lazymatch o with 36 => exact (rd_chunk_s32 _ _ _ _ _ C) end | exact (rd_chunk_u32 _ _ _ _ _ C) ] ]
end.
(* the end at RUN of a reader of kind kd with window [lo, hi) *)
Ltac rd_fin LAWS HJ0 Hfr Hk Hmo HC Hops Hkat Hpd Hc HAE B2 B33 g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kd pv dv od lo hi :=
lazymatch goal with
| HS : st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  KE : forall a, _ -> ~ rd_zone _ _ _ _ _ a -> _ |- _ =>
  let Ca := fresh "Ca" in let Cb := fresh "Cb" in
  rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb;
  rewrite ?ew_ewset_other in Ca, Cb by lia; rewrite B2 in Ca, Cb;
  rewrite ?wvb_collapse in HJm;
  lazymatch type of Ca with YP09.chunk_ok _ _ _ _ (YP09.mkChunk 152 (CVal 8 (SOff 35 ?j))) =>
  eapply (rd_end _ _ _ _ LAWS g pos sp1 ops ly2 S2 W2 regs2 mem2 md2 k c ys kd pv dv od lo hi Ef ssf msf _ j _ _ _ _
    HJ0 Hfr Hk Hmo HC Hops Hkat Hpd ltac:(lia) ltac:(lia) HJm
    ltac:(env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(lia) ltac:(lia) KE Ca Cb ltac:(lia) ltac:(lia));
  [ rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE | rd_field Hkat KE
  | first [lia | apply rd_u32_range] | first [lia | apply rd_u32_range] | first [lia | apply rd_u32_range]
  | first [lia | apply s32_range] ]
  end
end.
