(* Pieces of segment RD12 (SCRIBBLE_TEXT) of the image-A walk of LLVMFuzzerTestOneInput (lib/A/Prog/codec_amain_inv.v,
   seg_rd12). The segment is proved in three parts that chain by two inner cuts of the mcut form:
     0x80d70 .. 0x80d8c  the test of k.p (s7): when NULL, diginet_personality_of(1) and SPEC_C24 stored to k.p and
                         k.desk (rd12_Pa: a cursor past the op byte, the personality pair of a desk, k as HEAD left it
                         with that pair);
     0x80d8c .. 0x81294  k.a = fuzz_u8 & 0x7f, text_arg(&in, text) (rd12_Pb: the cursor after the text, k with a,
                         the 65 text bytes with a 0 among them);
     0x81294 .. 0x8210c  the chars byte at k.desk + 10, check_text_scribble(text, k.bytes, chars), kind 9, ENC9.
   Here: the two cuts; r12_exit, the cut at a stop of a run (rd_exit's form for any pc and cut fact); the record with
   p / desk replaced (r12_kat_pd) or kind / bytes replaced (r12_kat_kb); r12_call_kept, the cut facts across a call
   whose write set is the text, the record or the cursor (codec_amain_encl.v am_call_kept with that write set); the
   shadow of k.bytes; the text after text_arg; the one-byte region of the chars byte on the desk atom. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkKept CPgWalkCall CPgSat CPgTokJ.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_st codec_amain_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rdlib codec_amain_rdin codec_amain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ================================ the record with fields replaced ================================ *)
Definition kz_set_pd (k : kcallZ) (p d : Z) : kcallZ :=
mkKcallZ (kz_kind k) p d (kz_a k) (kz_b k) (kz_c k) (kz_delta k) (kz_bytes k) (kz_n k) (kz_rc k)
(kz_before k) (kz_out k) (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k).
Definition kz_set_kb (k : kcallZ) (kind : Z) (bs : list Z) : kcallZ :=
mkKcallZ kind (kz_p k) (kz_desk k) (kz_a k) (kz_b k) (kz_c k) (kz_delta k) bs (kz_n k) (kz_rc k)
(kz_before k) (kz_out k) (kz_want_rc k) (kz_want k) (kz_want_len k) (kz_want_key k) (kz_want_display k).

(* ================================ the text after text_arg ================================ *)
Definition r12_tb (dat tj : list Z) : list Z := text_takenZ dat ++ [0] ++ skipn (1 + text_lenZ dat) tj.
Lemma r12_tb_len : forall dat tj, length tj = 65%nat -> length (r12_tb dat tj) = 65%nat.
Proof.
intros dat tj Hl. unfold r12_tb, text_takenZ. rewrite !length_app, length_firstn, !length_skipn, Hl. cbn [length].
assert (H1 : (text_lenZ dat <= length dat - text_hdrZ dat)%nat) by (unfold text_lenZ; lia).
assert (H2 : (text_lenZ dat <= 64)%nat).
{ unfold text_lenZ. pose proof (Z.mod_pos_bound (text_u16Z dat) 65 ltac:(lia)) as M. lia. }
lia.
Qed.
Lemma r12_tb_in0 : forall dat tj, In 0 (r12_tb dat tj).
Proof. intros dat tj. unfold r12_tb. apply in_or_app. right. left. reflexivity. Qed.
Lemma r12_used_le : forall dat, (text_usedZ dat <= length dat)%nat.
Proof. intros dat. unfold text_usedZ, text_lenZ, text_hdrZ. lia. Qed.
(* the bytes of a garr8 are bytes *)
Lemma r12_garr8_bytes : forall segs (m : word -> option byte) a l, garr8 segs m a l -> Forall (fun x => 0 <= x < 256) l.
Proof.
intros segs m a l H. apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as (j & Hj & <-).
exact (proj2 (H j Hj)).
Qed.

(* the chars byte of the desk, a read-only region on the desk atom 37 holding the atom 38 *)
Definition r12_chr : YP09.region := YP09.mkRegion (Some 37%nat) 10 11 0 0 [YP09.mkChunk 10 (CVal 1 (SOff 38 0))].
(* the chars of the two desks *)
Lemma r12_pd_chars : forall pv dv d, pd_okA pv dv (Some d) -> 0 <= d_chars d <= 8.
Proof.
intros pv dv d [(_ & _ & H) | [(_ & _ & H) | (_ & _ & H)]]; [discriminate H | ..];
  injection H as ->; vm_compute; split; discriminate.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* ================================ the two inner cuts ================================ *)
(* 0x80d8c: past the test of k.p; the op byte taken, k.p / k.desk the personality pair of a desk *)
Definition rd12_Pa (g : ectx) (pos sp1 ops : Z)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\
exists c pv dv d, cur_at g sp1 c W2 mem2 /\ 1 <= c /\ pd_okA pv dv (Some d) /\ k_at g pos (k_rdZ 12 pv dv) W2 mem2.
(* 0x81294: text_arg returned; k.a stored, the 65 text bytes tb at F + 64 with a 0 among them *)
Definition rd12_Pb (g : ectx) (pos sp1 ops : Z)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\
exists c pv dv d a tb, cur_at g sp1 c W2 mem2 /\ pd_okA pv dv (Some d) /\ 0 <= a < 2 ^ 32 /\
k_at g pos (rdk 12 pv dv a 0 0 0 (repeat 0 24)) W2 mem2 /\
garr8 tfibsegs (rd W2 mem2) (FA g pos + 64) tb /\ length tb = 65%nat /\ In 0 tb.

(* ================================ the record ================================ *)
Lemma r12_kat_pd : forall g pos k (W : world tfibsegs) mem mem' p d,
k_at g pos k W mem ->
(forall x, FA g pos + 176 <= x < FA g pos + 360 -> ~ (FA g pos + 184 <= x < FA g pos + 200) ->
 aview tfibsegs (w_H W) mem' x = aview tfibsegs (w_H W) mem x) ->
0 <= p < 2 ^ 64 -> 0 <= d < 2 ^ 64 ->
val_mem tfibsegs (rd W mem') (FA g pos + 176 + 8) 8 p ->
val_mem tfibsegs (rd W mem') (FA g pos + 176 + 16) 8 d ->
k_at g pos (kz_set_pd k p d) W mem'.
Proof.
intros g pos k W mem mem' p d
  ((V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180) & Hwf)
  Hk Hp Hd Vp Vd.
unfold k_at. set (q := FA g pos + 176) in *.
assert (KV : forall o' n v, 0 <= o' -> o' + Z.of_nat n <= 184 -> (o' + Z.of_nat n <= 8 \/ 24 <= o') ->
  val_mem tfibsegs (rd W mem) (q + o') n v -> val_mem tfibsegs (rd W mem') (q + o') n v).
{ intros o' n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem mem'); [|exact Hv].
  intros x Hx. apply Hk; subst q; lia. }
assert (KG : forall o' l, 24 <= o' -> o' + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (rd W mem) (q + o') l -> garr8 tfibsegs (rd W mem') (q + o') l).
{ intros o' l H1 H2 Hg. apply (am_garr8_kept (w_H W) (w_H W) mem mem'); [|exact Hg].
  intros x Hx. apply Hk; subst q; lia. }
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbe & Lo & Lw).
split.
- unfold kz_set_pd, kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
  split; [rewrite <- (Z.add_0_r q); apply KV; [lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact V0]|].
  split; [exact Vp|]. split; [exact Vd|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V28]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
  split; [apply KG; [lia | rewrite Lb; cbn; lia | exact G40]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V64]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
  split; [apply KG; [lia | rewrite Lbe; cbn; lia | exact G76]|].
  split; [apply KG; [lia | rewrite Lo; cbn; lia | exact G108]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
  split; [apply KG; [lia | rewrite Lw; cbn; lia | exact G144]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V176]|].
  apply KV; [lia | cbn; lia | cbn; lia | exact V180].
- destruct Hwf as (W1 & _ & _ & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17).
  unfold kz_set_pd, kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
  repeat split; first [assumption | lia].
Qed.

Lemma r12_kat_kb : forall g pos k (W W' : world tfibsegs) mem mem' kind bs,
k_at g pos k W mem ->
(forall x, FA g pos + 180 <= x < FA g pos + 360 -> ~ (FA g pos + 216 <= x < FA g pos + 240) ->
 aview tfibsegs (w_H W') mem' x = aview tfibsegs (w_H W) mem x) ->
- 2 ^ 31 <= kind < 2 ^ 31 -> length bs = 24%nat ->
val_mem tfibsegs (rd W' mem') (FA g pos + 176) 4 kind ->
garr8 tfibsegs (rd W' mem') (FA g pos + 176 + 40) bs ->
k_at g pos (kz_set_kb k kind bs) W' mem'.
Proof.
intros g pos k W W' mem mem' kind bs
  ((V0 & V8 & V16 & V24 & V28 & V32 & V36 & G40 & V64 & V72 & G76 & G108 & V140 & G144 & V168 & V176 & V180) & Hwf)
  Hk Hkind Hl Vk Gb.
unfold k_at. set (q := FA g pos + 176) in *.
assert (KV : forall o' n v, 4 <= o' -> o' + Z.of_nat n <= 184 -> (o' + Z.of_nat n <= 40 \/ 64 <= o') ->
  val_mem tfibsegs (rd W mem) (q + o') n v -> val_mem tfibsegs (rd W' mem') (q + o') n v).
{ intros o' n v H1 H2 H3 Hv. apply (cw_val_mem_kept (w_H W) (w_H W') mem mem'); [|exact Hv].
  intros x Hx. apply Hk; subst q; lia. }
assert (KG : forall o' l, 64 <= o' -> o' + Z.of_nat (length l) <= 184 ->
  garr8 tfibsegs (rd W mem) (q + o') l -> garr8 tfibsegs (rd W' mem') (q + o') l).
{ intros o' l H1 H2 Hg. apply (am_garr8_kept (w_H W) (w_H W') mem mem'); [|exact Hg].
  intros x Hx. apply Hk; subst q; lia. }
pose proof Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Lb & Lbe & Lo & Lw).
split.
- unfold kz_set_kb, kcall_atA. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
  split; [exact Vk|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V8]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V16]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V24]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V28]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V32]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V36]|].
  split; [exact Gb|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V64]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V72]|].
  split; [apply KG; [lia | rewrite Lbe; cbn; lia | exact G76]|].
  split; [apply KG; [lia | rewrite Lo; cbn; lia | exact G108]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V140]|].
  split; [apply KG; [lia | rewrite Lw; cbn; lia | exact G144]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V168]|].
  split; [apply KV; [lia | cbn; lia | cbn; lia | exact V176]|].
  apply KV; [lia | cbn; lia | cbn; lia | exact V180].
- destruct Hwf as (_ & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13 & W14 & W15 & W16 & W17).
  unfold kz_set_kb, kcall_wfZ. cbn [kz_kind kz_p kz_desk kz_a kz_b kz_c kz_delta kz_bytes kz_n kz_rc kz_before kz_out
    kz_want_rc kz_want kz_want_len kz_want_key kz_want_display].
  repeat split; first [assumption | lia].
Qed.

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* ================================ the cut at a stop ================================ *)
(* s10 at a stop whose state keeps it as the base env's atom 26 *)
Lemma r12_ops : forall g pos c regs2 ys E ss (W : world tfibsegs) ms ops,
env_agree 35 (am_env g pos c regs2 ys) E -> YP0l.st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sr_get (ss_regs ss) 26%bv = SOff 26 0 -> ops_at ops regs2 -> ops_at ops (ms_regs ms).
Proof.
intros g pos c regs2 ys E ss W ms ops HAG HS H26 (Hops & R26). split; [exact Hops|].
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 26%bv HS), H26.
destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
Qed.

(* the executor state of a run's stop at pc, with the zone it wrote, is the cut at pc whose fact P the final
   registers and memory satisfy (codec_amain_rdlib.v rd_exit, for any pc and P) *)
Lemma r12_exit : forall g pos sp1 lo hi c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 pc
  (P : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 35 (am_env g pos c regs2 ys) E ->
YP0l.st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> 0 <= lo -> hi <= 184 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 lo hi a ->
 aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
P ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 ->
SRr tfibsegs W2 {| cfg_ms := ms; cfg_model := md3 |} (mcut B MT K XM_LIB g pos sp1 0 pc P).
Proof.
intros g pos sp1 lo hi c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 pc P
  HJ Hfr Hk Hmo HC HJ3 HAG HS Hpc Hresv Hkeep Hlo Hhi KE HP.
apply SRr_ret.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
rewrite Hpc in Ems.
destruct (rd_zone_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (Happ & Hf4096 & Hfc & Hsp0 & Hsp & Hsp47 & Hclo).
pose proof HS as HS'. rewrite Ems in HS'.
assert (HC3 : mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3).
{ apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    k (Z_to_bv 64 pc) ss E HC HJ3 HAG HS' Hkeep).
  - intros a Ha. apply KE.
    + unfold am_keepzone in Ha. lia.
    + exact (rd_keep_apart g pos sp1 lo hi a Hf4096 Hfc Hsp0 Hsp Hlo Hhi Ha).
  - intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    + unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
    + exact (rd_shadow_apart g pos sp1 lo hi i Happ Hf4096 Hfc Hsp0 Hsp Hclo Hlo Hhi Hi).
  - pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm. }
rewrite Ems. change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs pc (ms_regs ms) (ms_mem ms) md3).
exact (am_mcut B MT K XM_LIB g pos sp1 0 pc P ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k HJ3 Hfr Hk Hmo HC3 HP).
Qed.

(* ================================ across a call that writes the text, the record or the cursor ================================ *)
Lemma r12_call_kept : forall g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev T (Ef : Z -> Prop)
ly3 S3 W3 regs3 mem3 md3 k3,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 kev ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 kv ly2 S2 W2 regsc mem2 md2 ->
(forall a, Ef a -> (FA g pos + 64 <= a < FA g pos + 129) \/ (FA g pos + 176 <= a < FA g pos + 360) \/
   (sp1 + 152 <= a < sp1 + 168)) ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly3 S3 W3 mem3 md3 k3 ->
aregs_preserved regsc regs3 ->
Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
tcj_kept tfibsegs B T ly2 S2 W2 mem2 W3 mem3 (spZ regsc) Ef ->
mcommon B MT K XM_LIB g pos sp1 kv ly3 S3 W3 regs3 mem3 md3 /\
(forall a, FA g pos <= a < FA g pos + 512 -> ~ Ef a ->
 aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
Proof.
intros g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev T Ef ly3 S3 W3 regs3 mem3 md3 k3 HJ Hfr HC HEf HJ3 HPR HPerm HK.
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 kv ly2 S2 W2 regsc mem2 md2 kev HJ Hfr HC) as
  (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres & Hn & Hp & Hpn & Hblk).
pose proof HJ as (HAR & _).
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 3 pos HAR Hin) as (_ & _ & Happ).
assert (E512 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite EFA, E512 in Happ. rewrite E512 in Hfceil.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity.
destruct HC as (Hpre & Hsp1 & R2 & R9 & R8 & R3 & R4 & R20 & R18 & R21 & R22 & R25 & R19 & R27 & H64 &
  V16 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & V112 & V120 &
  S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104 & VFL & SHM & GIN & PERM).
assert (Usp : spZ regsc = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold AM_HI in *; lia).
rewrite Usp in HK. destruct HK as (K1 & _ & _ & K4 & _ & _).
set (F := FA g pos) in *.
unfold AM_HI in *.
(* the machine stack at or above sp1 off the cursor: kept by clause 1 *)
assert (KS : forall a, sp1 <= a < e_sp0 g -> ~ (sp1 + 152 <= a < sp1 + 168) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha Hc. apply K1; [lia | lia | intros He; pose proof (HEf a He); lia]. }
(* the frame and its shadow: kept by clause 4 off E *)
assert (KF : forall a, F <= a < F + 512 -> ~ Ef a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha He. apply (K4 3 pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA, E512; lia | exact He]. }
assert (KSH : forall i, 0 <= i < 56 ->
  aview tfibsegs (w_H W3) mem3 (shadow_addr F + i) = aview tfibsegs (w_H W2) mem2 (shadow_addr F + i)).
{ intros i Hi. apply (K4 3 pos _ Hin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFA, E512. change (512 / 8) with 64. lia.
  - intros He. pose proof (HEf _ He) as Hr. unfold shadow_addr, SHADOW_OFF in Hr.
    pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. lia. }
assert (VK : forall a n v, ((sp1 <= a /\ a + Z.of_nat n <= sp1 + 152) \/ (sp1 + 168 <= a /\ a + Z.of_nat n <= e_sp0 g)) ->
  val_mem tfibsegs (rd W2 mem2) a n v -> val_mem tfibsegs (rd W3 mem3) a n v).
{ intros a n v H1 Hv. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
  intros x Hx. apply KS; lia. }
assert (P2 : getr regs3 2 = getr regsc 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr regsc 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr regsc 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr regsc 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr regsc 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr regsc 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr regsc 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs3 20 = getr regsc 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs3 21 = getr regsc 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs3 22 = getr regsc 22) by exact (HPR 22 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs3 25 = getr regsc 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P27 : getr regs3 27 = getr regsc 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
pose proof Hpre as Hpre'. unfold e_pre, codec_lib_pre_x in Hpre'.
destruct Hpre' as (_ & _ & _ & _ & _ & Hnpl & _).
split.
- refine (conj Hpre (conj Hsp1 _)).
  rewrite P2, P9, P8, P3, P4, P20, P18, P21, P22, P25, P19, P27.
  refine (conj R2 (conj R9 (conj R8 (conj R3 (conj R4 (conj R20 (conj R18 (conj R21 (conj R22 (conj R25
    (conj R19 (conj R27 (conj H64 _))))))))))))).
  split; [apply VK; [cbn; lia | exact V16]|].
  split; [apply VK; [cbn; lia | exact V24]|].
  split; [apply VK; [cbn; lia | exact V32]|].
  split; [apply VK; [cbn; lia | exact V40]|].
  split; [apply VK; [cbn; lia | exact V48]|].
  split; [apply VK; [cbn; lia | exact V56]|].
  split; [apply VK; [cbn; lia | exact V64]|].
  split; [apply VK; [cbn; lia | exact V72]|].
  split; [apply VK; [cbn; lia | exact V80]|].
  split; [apply VK; [cbn; lia | exact V88]|].
  split; [apply VK; [cbn; lia | exact V96]|].
  split; [apply VK; [cbn; lia | exact V104]|].
  split; [apply VK; [cbn; lia | exact V112]|].
  split; [apply VK; [cbn; lia | exact V120]|].
  split; [apply VK; [cbn; lia | exact S8]|].
  split; [apply VK; [cbn; lia | exact S16]|].
  split; [apply VK; [cbn; lia | exact S24]|].
  split; [apply VK; [cbn; lia | exact S32]|].
  split; [apply VK; [cbn; lia | exact S40]|].
  split; [apply VK; [cbn; lia | exact S48]|].
  split; [apply VK; [cbn; lia | exact S56]|].
  split; [apply VK; [cbn; lia | exact S64]|].
  split; [apply VK; [cbn; lia | exact S72]|].
  split; [apply VK; [cbn; lia | exact S80]|].
  split; [apply VK; [cbn; lia | exact S88]|].
  split; [apply VK; [cbn; lia | exact S96]|].
  split; [apply VK; [cbn; lia | exact S104]|].
  split.
  { apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact VFL].
    intros x Hx. cbn in Hx. apply KF; [lia|]. intros He. pose proof (HEf x He). lia. }
  split; [intros i Hi; etransitivity; [exact (KSH i Hi) | exact (SHM i Hi)]|].
  split; [|exact (Permutation_trans HPerm PERM)].
  destruct (Z.eq_dec (e_n g) 0) as [Hn0 | Hn0].
  + intros j Hj. exfalso. rewrite length_map in Hj. lia.
  + destruct (Hblk ltac:(lia)) as (Hb2 & Hb0).
    assert (Hb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb2]).
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J2 & _).
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & J3 & _).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (am_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact GIN].
    intros x Hx. rewrite length_map in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    rewrite (J3 (e_p g) (e_n g) (x - e_p g) Hb0 Hb3 ltac:(lia) (inFP_nil _)).
    rewrite (J2 (e_p g) (e_n g) (x - e_p g) Hb0 Hb2 ltac:(lia) (inFP_nil _)). reflexivity.
- exact KF.
Qed.

(* ================================ shadow and regions ================================ *)
(* k.bytes (24 bytes at F + 216) when k's 23 shadow bytes are 0 *)
Lemma r12_bs_bytes : forall g pos sp1 ly2 S2 W2 regs2 mem2 md2,
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
block_shadow (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (FA g pos + 216) 24.
Proof.
intros g pos sp1 ly2 S2 W2 regs2 mem2 md2 HC.
pose proof HC as HF64. do 14 (destruct HF64 as (_ & HF64)). destruct HF64 as (HF64 & _).
pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
apply am_block_shadow; [exact HF64 | lia | reflexivity | lia |].
intros i Hi. change ((24 + 7) / 8) with 3 in Hi. change (24 / 8) with 3. change (216 / 8) with 27.
rewrite (proj2 (Z.ltb_lt i 3) ltac:(lia)).
rewrite (HSH' (27 + i) ltac:(lia)). f_equal.
pose proof amain_pure_sat as (_ & _ & _ & _ & _ & _ & _ & Hk23 & _).
apply (Hk23 0 (Z.to_nat (27 + i))). lia.
Qed.

(* the chars byte's region at a state of the journal *)
Lemma r12_chr_ok : forall E (W : world tfibsegs) mem pv dv d,
arodata_ok B (aview tfibsegs (w_H W) mem) -> pd_okA pv dv (Some d) ->
ew E 37 = Z_to_bv 64 dv -> ew E 38 = Z_to_bv 64 (d_chars d) ->
region_ok tfibsegs E (rd W mem) r12_chr.
Proof.
intros E W mem pv dv d HR Hpd E37 E38.
destruct (pd_range_A pv dv d Hpd) as (_ & Hd & _). unfold CM_SPEC_C24, CM_SPEC_PC in Hd.
pose proof (r12_pd_chars pv dv d Hpd) as Hc.
unfold region_ok, r12_chr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E37, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val tfibsegs E _ dv 10 1 (SOff 38 0) (d_chars d)).
- cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
- lia.
- change (N.to_nat 1) with 1%nat. apply val_mem1_of_aviewA.
  pose proof (adesk_bytes_of_pd B TL W mem pv dv d 2 HR Hpd ltac:(lia)) as X.
  replace (dv + 8 + 2) with (dv + 10) in X by lia. exact X.
Qed.
End b.
End a.
