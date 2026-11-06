(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 630 of its 709 lines of code are new or changed and 1193 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsg1.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SEG1 of ZZpsclose.ps_close on image B (fs.asan-ubsan, put_string 0x85fc8) - put_string's entry, the fake-frame
   grant, the opening-quote put at PS_OPEN_CALL 0x860d8 and its return PS_OPEN_RET 0x860dc, in ps_inv.
   Route (all reused by name): FSW_put_string.ps_to_put1 (entry, grant, stretch to the call) -> ps_aj_raise (the
   journal's window top from the entry sp to ot) -> ps_put_call (the call, U0 = U) -> ZZpsres.psr_resume (the
   return shape ps_ret_ss PS_OPEN_RET L psj_scs0 [ps_str_region L]); then ps_inv's fields.
   Image B's change against A: put_string keeps the string s in s2 = x18 (image A: s10 = x26), so the call-site
   register read R18, the callee-saved carry P18, the env atom V18, the string region (atom 18) and ps_inv's and
   psr_resume's string register are on 18. MEASURED on image B (vm_compute of ps_ss_put, fsw_ps_tbl): pc A_put
   0x8449c; ra = PS_OPEN_RET, a0 = x10 = atom 19 (s3 = o), a1 = PS_Q1 0x21240, a2 = 1, x18 = atom 18, x21 = x24 =
   atom 10 (the fake frame), x22 = atom 47, x23 = atom 32; regions [47: the frame's shadow f1 f1 f1 f1 f8 f3 f3 f3;
   8: the 13 saved words at -8 .. -104; 9: [0, 88) with the slot +80 = atom 10; 10: the fake frame header 0x41b58ab3,
   74709, 0x85fc8 (548808), flag at +56]; STK_put_string and STK_put are computed from their definitions in the
   proof (vm_compute at elaboration), never pinned.
   What is carried over the prologue (entry mem -> call memc): every byte at or above the entry sp and every live
   block byte, by the journal's high clause and ps_to_put1's block clause (pske_agree with Wr = the complement of
   that set, psg1_KP); the statics and the read-only view by ps_to_put1's image clause and HIMG's first conjunct.
   The quote string is ZZpsg1k.ps_quote_src; fs_heads and the buffer head at the return are ZZpsg1k.ps_heads_put;
   cstr_ok and wsrc_kept at the return are ZZpsg3k.ps_str_keep; the read-only view at the return is
   FSW_rd.arodata_kept_own over the entry-to-return journal.
   Templates (cited): psg1_str_home is the text of ZZpssep.pss_str_off_fr's Hloc (lib/A/ZZpssep.v:243-253);
   psg1_chunk_lit1 follows ZZpsjoin.psj_chunk_f8 (lib/A/ZZpsjoin.v:311-321).
   Statement check: psg1_fits := ps_close B psg1 typechecks, so psg1's type IS ps_close's first premise.
   Section hypotheses used: HPUT (ps_put_call), HSS HENV HML HSMP HSM0 HSMPC HGUAR HUCELL (ps_to_put1), HIMG
   (ps_quote_src, ps_str_keep, the statics). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3 FSW_strkit FSW_rd FSW_put_string ZZpsjoin ZZpsclose ZZpskeep ZZpsmodel ZZpssep ZZpsres ZZpsg1k ZZpsg3k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterRet.
(* the image's four loaded segments by name (ZZpssep's pattern); Required, not Imported *)
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic and small facts (lia only here) ================= *)
Lemma psg1_sp1 : forall sp0, sp0 mod 16 = 0 ->
  (32 * ((sp0 - PS_FRAME_OWN) / 32)) mod 32 = 0 /\
  sp0 - 208 <= 32 * ((sp0 - PS_FRAME_OWN) / 32) <= sp0 - 192.
Proof.
intros sp0 H. unfold PS_FRAME_OWN. split.
- rewrite Z.mul_comm. apply Z_mod_mult.
- Z.div_mod_to_equations. lia.
Qed.

Lemma psg1_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. Z.div_mod_to_equations. lia. Qed.

Lemma psg1_nn : forall P Q : Prop, P \/ ~ P -> (P -> Q) -> ~ ~ P -> Q.
Proof. intros P Q [H | H] K N; [exact (K H) | exfalso; exact (N H)]. Qed.

(* the bytes the prologue keeps: at or above the entry sp, or in a live block of the entry *)
Definition psg1_KP (lo : Z) (A : list (Z * Z)) (a : Z) : Prop :=
  lo <= a < 2 ^ 64 \/ Exists (fun bm : Z * Z => fst bm <= a < fst bm + req_size (snd bm)) A.

Lemma psg1_kp_dec : forall lo A a, psg1_KP lo A a \/ ~ psg1_KP lo A a.
Proof.
intros lo A a. unfold psg1_KP.
assert (Pd : forall bm : Z * Z,
  {fst bm <= a < fst bm + req_size (snd bm)} + {~ (fst bm <= a < fst bm + req_size (snd bm))}).
{ intros bm. destruct (Z_le_dec (fst bm) a) as [H1 | H1];
    [destruct (Z_lt_dec a (fst bm + req_size (snd bm))) as [H2 | H2]; [left; lia | right; lia] | right; lia]. }
destruct (@Exists_dec _ _ A Pd) as [E | E]; [left; right; exact E|].
destruct (Z_le_dec lo a) as [H1 | H1].
- destruct (Z_lt_dec a (2 ^ 64)) as [H2 | H2]; [left; left; lia|].
  right. intros [H | H]; [lia | exact (E H)].
- right. intros [H | H]; [lia | exact (E H)].
Qed.

(* two intervals are apart when no point of the first lies in the second *)
Lemma psg1_disj_pt : forall s n f m, 0 < n -> 0 < m ->
  (forall x, s <= x < s + n -> ~ (f <= x < f + m)) -> s + n <= f \/ f + m <= s.
Proof.
intros s n f m Hn Hm H.
destruct (Z_le_gt_dec (s + n) f) as [H1 | H1]; [left; exact H1|].
destruct (Z_le_gt_dec (f + m) s) as [H2 | H2]; [right; exact H2|].
exfalso. apply (H (Z.max s f)); lia.
Qed.

(* the string (application memory, amem_range) and the frame's eight shadow bytes are apart *)
Lemma psg1_sh_str : forall {rc : YM05.RunCeil} s L F ac, amem_range s (L + 8) -> 0 <= L -> 4096 <= F ->
  F + 64 <= ac -> ac <= 0x7fffff800000 ->
  s + (L + 1) <= shadow_addr F \/ shadow_addr F + 8 <= s.
Proof.
intros rc s L F ac Ha HL HF HFc Hac. pose proof asan_consts as (_ & _ & C3 & C4 & C5).
unfold amem_range in Ha. rewrite C3, C4, C5 in Ha. unfold shadow_addr, SHADOW_OFF.
Z.div_mod_to_equations. lia.
Qed.

Lemma psg1_regwf_str : forall L, 0 <= L -> YP09.regions_wf [ps_str_region L] = true.
Proof.
intros L HL. unfold ps_str_region. cbn [YP09.regions_wf]. unfold YP09.region_wf.
cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
replace (0 <=? L + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma psg1_wmax1 : forall (text bs : list Z), plain_bytes bs ->
  Z.of_nat (length text) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= FSH_Fn_writer.WMAX ->
  Z.of_nat (length text) + 1 + 1 <= FSH_Fn_writer.WMAX.
Proof. intros text bs Hp H. rewrite (wstr_plain_length bs Hp) in H. lia. Qed.

(* fuzz/alloc.c's statics are writable image bytes, so no read-only byte *)
Lemma psg1_pstat_not_ro : forall a, inFP FS_PSTAT_FP a -> ~ in_roP tfibsegs FS_RLO FS_RHI a.
Proof.
intros a HP Hro. pose proof (pss_pstat_rng a HP) as [H1 H2].
destruct Hro as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
assert (E : tfibsegs = [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003]) by reflexivity.
rewrite E in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn in Hw, Hr; try discriminate Hw; lia.
Qed.

(* one register of the call-site state, read through its symbolic value *)
Lemma psg1_reg : forall {fx : YK11.FPState} (H : word -> bool) E ms (r : bv 5) n,
  st_ok tfibsegs E ps_ss_put (restrict H ms) -> sr_get (ss_regs ps_ss_put) r = SOff n 0 ->
  YK11.getr (ms_regs ms) r = ew E n.
Proof.
intros fx H E ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ps_ss_put ms r HS), Hr. apply fsw_SOff0.
Qed.

(* a byte the unpoisoned views agree on, off the image: its mbyte and its presence *)
Lemma psg1_view_pt : forall (H : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> aview tfibsegs H m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a /\ (apresent H m a -> apresent H m' a).
Proof.
intros H m m' a Ha Hni E.
pose proof (seg_rom_none tfibsegs a Ha Hni) as R.
unfold aview in E. cbv beta in E. unfold apresent.
unfold mbyte, mrestrict in E |- *.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- split; [reflexivity | intros (Hf & _); discriminate Hf].
- destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E', (m (Z_to_bv 64 a)) as [b|] eqn:Em;
    rewrite ?R in E |- *; cbn in E |- *.
  + injection E as E. assert (b' = b) as -> by (apply bv_eq; exact E).
    split; [reflexivity | intros _; split; [reflexivity | eexists; reflexivity]].
  + discriminate E.
  + discriminate E.
  + split; [reflexivity | intros (_ & bb & Hb); discriminate Hb].
Qed.

Lemma psg1_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E. cbv beta in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn [option_map] in E; try discriminate E; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma psg1_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
destruct (rd a) as [b0|]; [|exfalso; exact (H0 eq_refl)].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.

Lemma psg1_glob_keep : forall (W W' : world tfibsegs) (mem mem' : word -> option byte) live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a ->
     mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a) ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' live peak cnt fail K (V1 & V2 & V3 & V4 & R).
pose proof pske_pstat_in as (P1 & P2 & P3 & P4).
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
          val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv k Hk. rewrite K; [exact (Hv k Hk)|].
  exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
exact (conj (VK _ _ P1 V1) (conj (VK _ _ P2 V2) (conj (VK _ _ P3 V3) (conj (VK _ _ P4 V4) R)))).
Qed.

(* the saved-word chunks read the same at two envs that agree on the thirteen saved-word atoms *)
Lemma psg1_sv_env : forall {fx : YK11.FPState} E E' (m : word -> option byte) b,
  (forall k, (k < 13)%nat -> ew E' (xatom k) = ew E (xatom k)) ->
  Forall (YP09.chunk_ok tfibsegs E m b) ps_sv_chunks -> Forall (YP09.chunk_ok tfibsegs E' m b) ps_sv_chunks.
Proof.
intros fx E E' m b HE H. unfold ps_sv_chunks in *.
rewrite Forall_map in H |- *. rewrite Forall_forall in H |- *.
intros k Hk. pose proof (proj1 (in_seq _ _ _) Hk) as Hk'.
apply (ps_chunk_transfer E E' m b _ 8 (SOff (xatom k) 0) (SOff (xatom k) 0)); [|exact (H k Hk)].
rewrite !fsw_SOff0. symmetry. apply HE. lia.
Qed.

(* a one-byte literal chunk read back as another literal of the same low byte (template ZZpsjoin.psj_chunk_f8) *)
Lemma psg1_chunk_lit1 : forall {fx : YK11.FPState} E E' (m m' : word -> option byte) b off z1 z2,
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 1 (SLit z1))) ->
  byte_of_word (Z_to_bv 64 (zcanon z1)) 0 = byte_of_word (Z_to_bv 64 (zcanon z2)) 0 ->
  mbyte tfibsegs m' (b + off) = mbyte tfibsegs m (b + off) ->
  YP09.chunk_ok tfibsegs E' m' b (YP09.mkChunk off (CVal 1 (SLit z2))).
Proof.
intros fx E E' m m' b off z1 z2 H Hb Hm i Hi. cbn in Hi. assert (i = 0) as -> by lia.
destruct (H 0 ltac:(cbn; lia)) as (bb & H1 & H2). exists bb. split.
- cbn [YP09.cbyte YP09.c_val YP09.c_off] in H1 |- *. rewrite psl_lit_denot in H1 |- *.
  rewrite <- H1. f_equal. symmetry. exact Hb.
- cbn [YP09.c_off] in H2 |- *. rewrite Z.add_0_r in H2 |- *. rewrite Hm. exact H2.
Qed.

(* a raised layout keeps the frame, flag and top addresses *)
Lemma psg1_ly_addr : forall n ly ly' cid pos, layout_le n ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos /\
  ly_top ly' = ly_top ly.
Proof.
intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _ & _ & ET & _).
unfold frame_addr, flag_addr. rewrite EF. auto.
Qed.

(* the string region is apart from the five fixed regions of the return shape (image B: the string on atom 18) *)
Lemma psg1_dj_str : forall E scs sp0 sp1 F FL s L,
  bv_unsigned (ew E 8) = sp0 -> bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 24) = F ->
  bv_unsigned (ew E 47) = shadow_addr F -> bv_unsigned (ew E (xatom 13)) = FL -> bv_unsigned (ew E 18) = s ->
  s + (L + 1) <= sp1 -> sp1 + 192 <= sp0 ->
  (s + (L + 1) <= F \/ F + 64 <= s) -> (s + (L + 1) <= shadow_addr F \/ shadow_addr F + 8 <= s) ->
  (s + (L + 1) <= FL \/ FL + 1 <= s) ->
  Forall (fun r0 => YP09.all_disjoint E r0 [ps_str_region L]) (ps_ret_regions scs []).
Proof.
intros E scs sp0 sp1 F FL s L V8 V9 V24 V47 V46 V18 H1 H2 H3 H4 H5.
unfold ps_ret_regions, ps_str_region.
repeat apply Forall_cons; try apply Forall_nil;
  cbn [YP09.all_disjoint]; (split; [|exact I]); unfold YP09.extent_disjoint;
  cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi]; rewrite ?V8, ?V9, ?V24, ?V47, ?V46, ?V18; lia.
Qed.

Lemma psg1_str_ok : forall E (m : word -> option byte) s L, bv_unsigned (ew E 18) = s -> 0 <= s ->
  s + (L + 1) <= 2 ^ 64 -> Forall (YP09.region_ok tfibsegs E m) [ps_str_region L].
Proof.
intros E m s L V Hs Hs2. constructor; [|constructor].
unfold YP09.region_ok, ps_str_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite V. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | constructor].
Qed.

(* one of the frame's eight shadow chunks at put #1's call site, read as ps_fsh_chunks states it *)
Ltac psg1_sh C MSH k z1 z2 :=
  refine (psg1_chunk_lit1 _ _ _ _ _ k z1 z2 _ _ (MSH k ltac:(lia)));
  [ apply (proj1 (Forall_forall _ _) C); cbn [In]; repeat (first [left; reflexivity | right])
  | apply bv_eq; vm_compute; reflexivity ].

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* FSW_put_string's Section W hypotheses this segment uses (ps_to_put1 takes HSS .. HUCELL, ps_put_call HPUT) *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HENV : api_env tfibsegs B.
Hypothesis HML : model_laws (as_universe B).
Hypothesis HSMP : stack_malloc_progressP B.
Hypothesis HSM0 : astack_malloc_realizesU tfibsegs B 0.
Hypothesis HSMPC : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0.
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.
(* fs's image facts (RELOC / RUNTIME-owned; approved by a Theorem Labs lane 2026-10-29 as an open hypothesis of the walk): the
   quote string's bytes (ps_quote_src), the statics off the owned image, and the string's table arm (ps_str_keep) *)
Hypothesis HIMG : fs_img_facts tfibsegs B.

(* where a byte of the scanned string lives at a later state: a live block there, or the image
   (the text of ZZpssep.pss_str_off_fr's Hloc, ZZpssep.v:243-253) *)
Lemma psg1_str_home : forall ly S U (W : world tfibsegs) mem buf s (bs : list Z) ly' S',
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) ->
  (forall p n, In (p, n) (ablocks B ly S) -> p <> buf - HEAD -> In (p, n) (ablocks B ly' S')) ->
  forall x, s <= x < s + Z.of_nat (length bs) + 1 ->
  (exists p k, In (p, k) (ablocks B ly' S') /\ p <= x < p + req_size k) \/ in_img tfibsegs x.
Proof.
intros ly S U W mem buf s bs ly' S' Hsk Hkeep x Hx.
unfold FSH_Fn_writer.wsrc_kept in Hsk.
destruct Hsk as [(E & _) | [(p & k & Hne & HRB & Hp & Hk) | [(p & k & Hne & Hblk & Hp & Hk & _) | (l & Hl & Hlen)]]].
- exfalso. destruct bs; discriminate E.
- destruct HRB as (Hblk & _). left. exists (p - HEAD), (k + HEAD). split.
  + exact (Hkeep _ _ Hblk (pss_neq_head p buf Hne)).
  + rewrite pss_len0 in Hk. exact (pss_in_rblk p k s x _ Hp Hk Hx).
- left. exists p, k. split.
  + exact (Hkeep _ _ Hblk Hne).
  + rewrite pss_len0 in Hk. exact (pss_in_blk p k s x _ Hp Hk Hx).
- right. exact (pss_img_seg0 x (pss_ro_x s l bs x Hl Hlen Hx)).
Qed.

(* ================= SEG1 of ps_close ================= *)
Lemma psg1 :
  forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     (Q : world tfibsegs -> config -> Prop),
   ps_pre B ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   (forall pos lyc ly' S' U' W' regs' mem' md' buf',
      ps_inv B ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        [[34]] PS_OPEN_RET (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
        ly' S' U' W' regs' mem' md' buf' ->
      SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 PS_OPEN_RET) mem' (seg_rom tfibsegs)) md') Q) ->
   SRr tfibsegs W (cfg_at tfibsegs A_put_string regs mem md) Q.
Proof.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail Q PRE KONT.
destruct PRE as (HPRE & Hheads & Hfr & G10 & G11 & HOUT & HGLOB & HHEAD & Hspo & Hoot & Hot16 & Hottop & Hchain &
  HFPo & HPRESENT & Hcstr & Hsrck & Hbok & Hnz & Hplain & Hsep & Hwmax & Hcap & Hlive & Hbp).
clear Hsep HFPo Hnz Hbok.
destruct HPRE as (HPREa & HRO).
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREa) as (Hal16 & Hceil0 & H47 & _).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREa) as HARU0.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU0) as HAR0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 HPREa) as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hshi47 & _ & _ & Htop2).
(* the two budgets computed from their definitions at elaboration time: identical today, and they follow a budget
   change in S0 with no edit (a Theorem Labs lane 15:0xZ: STK_RT_REALLOC grows to ASTACK + 0x8a0) *)
assert (FS : STK_put_string = ltac:(let v := eval vm_compute in STK_put_string in exact v))
  by (vm_compute; reflexivity).
assert (FSP : STK_put = ltac:(let v := eval vm_compute in STK_put in exact v)) by (vm_compute; reflexivity).
pose proof (psg1_sp1 (spZ regs) Hal16) as (Hsp1m & Hsp1l & Hsp1h).
(* put's own facts at the entry *)
assert (Hbufblk : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)).
{ intros Hc. unfold FSH_Fn_writer.wout_ok in HOUT.
  destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & _) | (_ & HRB & _)]);
    [exfalso; exact (Hc E0) | exact (proj1 HRB)]. }
assert (Hcb0 : cap = 0 -> buf = 0).
{ intros Hc. unfold FSH_Fn_writer.wout_ok in HOUT.
  destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(_ & Eb & _) | (_ & HRB & _)]);
    [exact Eb | destruct HRB as (_ & _ & Hn & _); lia]. }
assert (Hcap0 : 0 <= cap).
{ unfold FSH_Fn_writer.wout_ok in HOUT. destruct HOUT as (_ & _ & _ & _ & _ & (Hc & _) & _). exact Hc. }
pose proof Hcstr as (Hcs1 & Hs4096 & HsL & Hs32 & Hamem & Hcsr).
(* ---- the entry, the grant, the stretch to the opening put's call ---- *)
apply (ps_to_put1 B HSS HENV HML HSMP HSM0 HSMPC HGUAR HUCELL ly S U W regs mem md ch
  (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) Q HPREa Hfr).
intros pos S2 regs2 md2 ms mat Hfrs Hab Hnev Hbb E8 E9 E2 E10 E19 E18 E3 E4 HS HJ HARUc Kblk Kimg.
remember (32 * ((spZ regs - PS_FRAME_OWN) / 32)) as sp1 eqn:Esp1.
assert (HIDE : Some sp1 = Some (32 * ((spZ regs - PS_FRAME_OWN) / 32))) by (f_equal; exact Esp1).
clear Esp1.
set (E0 := ewset (Ereg regs2 (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos))) 47
             (Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos)))) in *.
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem ms) _ HARUc) as HARc.
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U (ms_mem ms)) _ 0 pos HARc Hin2)
  as (HF4096 & HFce & HFapp).
change (fs_frame_bytes 0) with 64 in HFce, HFapp.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U (ms_mem ms)) _ 0 pos HARc Hin2) as (HFal & _).
assert (HShb : 0 <= shadow_addr (frame_addr ly 0 pos) /\ shadow_addr (frame_addr ly 0 pos) + 8 <= alloc_ceiling).
{ apply psr_sh_bd; lia. }
(* ---- the call-site registers (MEASURED in ps_ss_put) ---- *)
assert (RG : forall (r : bv 5) n, sr_get (ss_regs ps_ss_put) r = SOff n 0 -> n <> 47%nat ->
  YK11.getr (ms_regs ms) r = ew (Ereg regs2 (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos))) n).
{ intros r n Hr Hn. rewrite (psg1_reg _ _ ms r n HS Hr). unfold E0. apply ew_ewset_other. exact Hn. }
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 PS_OPEN_RET)
  by exact (fsw_reg_lit (w_H W) _ ps_ss_put ms 1%bv 549084 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R11 : YK11.getr (ms_regs ms) 11%bv = Z_to_bv 64 PS_Q1)
  by exact (fsw_reg_lit (w_H W) _ ps_ss_put ms 11%bv 135744 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R12 : YK11.getr (ms_regs ms) 12%bv = Z_to_bv 64 1)
  by exact (fsw_reg_lit (w_H W) _ ps_ss_put ms 12%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (RG 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 2 2%bv eq_refl) E2)).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv)
  by exact (eq_trans (RG 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 3 3%bv eq_refl) E3)).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv)
  by exact (eq_trans (RG 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 4 4%bv eq_refl) E4)).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (spZ regs)).
{ refine (eq_trans (RG 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                   (eq_trans (ew_Ereg_nat regs2 _ 8 8%bv eq_refl) (eq_trans E8 _))).
  symmetry. apply (Z_to_bv_bv_unsigned 64). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1)
  by exact (eq_trans (RG 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 9 9%bv eq_refl) E9)).
assert (R10 : YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 o)
  by exact (eq_trans (RG 10%bv 19%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 19 19%bv eq_refl) (eq_trans E19 G10))).
assert (R19 : YK11.getr (ms_regs ms) 19%bv = Z_to_bv 64 o)
  by exact (eq_trans (RG 19%bv 19%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 19 19%bv eq_refl) (eq_trans E19 G10))).
assert (R21 : YK11.getr (ms_regs ms) 21%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by exact (eq_trans (RG 21%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 10 10%bv eq_refl) E10)).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by exact (eq_trans (RG 24%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 10 10%bv eq_refl) E10)).
(* image B: s2 = x18 holds the string s (image A: s10 = x26) *)
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 s)
  by exact (eq_trans (RG 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(discriminate))
                     (eq_trans (ew_Ereg_nat regs2 _ 18 18%bv eq_refl) (eq_trans E18 G11))).
assert (R22 : YK11.getr (ms_regs ms) 22%bv = Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))).
{ rewrite (psg1_reg _ _ ms 22%bv 47 HS ltac:(vm_compute; reflexivity)). unfold E0. apply ew_ewset_same. }
assert (R23 : YK11.getr (ms_regs ms) 23%bv = Z_to_bv 64 SHADOW_OFF).
{ rewrite (RG 23%bv 32%nat ltac:(vm_compute; reflexivity) ltac:(discriminate)).
  change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (Usp : spZ (ms_regs ms) = sp1).
{ unfold spZ. transitivity (bv_unsigned (Z_to_bv 64 sp1)); [exact (f_equal bv_unsigned R2) | apply wz; lia]. }
assert (Us0 : s0Z (ms_regs ms) = spZ regs).
{ unfold s0Z. transitivity (bv_unsigned (Z_to_bv 64 (spZ regs)));
    [exact (f_equal bv_unsigned R8) | apply wz; unfold spZ; apply u64_range]. }
assert (Ura : raZ (ms_regs ms) = PS_OPEN_RET).
{ unfold raZ. transitivity (bv_unsigned (Z_to_bv 64 PS_OPEN_RET));
    [exact (f_equal bv_unsigned R1) | apply wz; unfold PS_OPEN_RET; lia]. }
(* the call-site env's atoms *)
assert (U8 : bv_unsigned (ew E0 8) = spZ regs).
{ unfold E0. rewrite ew_ewset_other by discriminate. rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl).
  exact (f_equal bv_unsigned E8). }
assert (U9 : bv_unsigned (ew E0 9) = sp1).
{ unfold E0. rewrite ew_ewset_other by discriminate. rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl).
  transitivity (bv_unsigned (Z_to_bv 64 sp1)); [exact (f_equal bv_unsigned E9) | apply wz; lia]. }
assert (U10 : bv_unsigned (ew E0 10) = frame_addr ly 0 pos).
{ unfold E0. rewrite ew_ewset_other by discriminate. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl).
  transitivity (bv_unsigned (Z_to_bv 64 (frame_addr ly 0 pos))); [exact (f_equal bv_unsigned E10) | apply wz; lia]. }
assert (U47 : bv_unsigned (ew E0 47) = shadow_addr (frame_addr ly 0 pos)).
{ unfold E0. rewrite ew_ewset_same. apply wz. lia. }
assert (Ux0 : bv_unsigned (ew E0 (xatom 0)) = raZ regs).
{ unfold E0. rewrite ew_ewset_other by (unfold xatom; discriminate). rewrite ps_ew_x. reflexivity. }
assert (Ux1 : bv_unsigned (ew E0 (xatom 1)) = s0Z regs).
{ unfold E0. rewrite ew_ewset_other by (unfold xatom; discriminate). rewrite ps_ew_x. reflexivity. }
(* ---- the call-site regions (MEASURED in ps_ss_put: 47 the frame's shadow, 8 the saved words, 9 the
   re-aligned frame, 10 the fake frame) ---- *)
pose proof (fsw_region_nth E0 ps_ss_put (restrict (w_H W) ms) 1
  (YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks) HS ltac:(vm_compute; reflexivity)) as R8ok.
cbn [ms_mem restrict] in R8ok.
pose proof R8ok as (_ & _ & _ & C8). cbn [YP09.r_base YP09.r_chunks base_val] in C8. rewrite U8 in C8.
pose proof (fsw_region_nth E0 ps_ss_put (restrict (w_H W) ms) 0 _ HS eq_refl) as R47ok.
cbn [ms_mem restrict] in R47ok.
destruct R47ok as (_ & _ & _ & C47). cbn [YP09.r_base YP09.r_chunks base_val] in C47. rewrite U47 in C47.
pose proof (fsw_region_nth E0 ps_ss_put (restrict (w_H W) ms) 2 _ HS eq_refl) as R9ok.
cbn [ms_mem restrict] in R9ok.
destruct R9ok as (_ & _ & _ & C9). cbn [YP09.r_base YP09.r_chunks base_val] in C9. rewrite U9 in C9.
pose proof (fsw_region_nth E0 ps_ss_put (restrict (w_H W) ms) 3 _ HS eq_refl) as R10ok.
cbn [ms_mem restrict] in R10ok.
destruct R10ok as (_ & _ & _ & C10). cbn [YP09.r_base YP09.r_chunks base_val] in C10. rewrite U10 in C10.
(* ---- the config at the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E0 ps_ss_put ms HS eq_refl).
change (ss_pc ps_ss_put) with A_put.
change (mkCfg (mkst (ms_regs ms) (Z_to_bv 64 A_put) (ms_mem ms) (seg_rom tfibsegs))
          (with_vm_backing (m_vm_lazy md2) mat md2))
  with (cfg_at tfibsegs A_put (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2)).
(* ---- what the prologue keeps: every byte at or above the entry sp, and every live block byte ---- *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _ & _ & _ & _ & J14 & _).
assert (HAGU : forall a, spZ regs <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. apply J9; lia. }
assert (KEEP : forall a, psg1_KP (spZ regs) (ablocks B ly S) a ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a /\ ~ in_img tfibsegs a /\ 0 <= a < 2 ^ 64).
{ intros a [Ha | Ha].
  - assert (Hhi : kHighMemBeg <= a) by lia.
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (fs_segs_img a Hi); unfold FS_IMG_END in *; lia).
    refine (conj _ (conj Hni Ha64)).
    rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms)) (ms_mem ms) a
                 (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc Ha64 (or_intror Hhi))).
    rewrite <- (aview_at tfibsegs (w_H W) (unpoison U mem) mem a
                 (unpoison_app B ly S U W mem md a HARU0 Ha64 (or_intror Hhi))).
    exact (HAGU a Ha).
  - apply Exists_exists in Ha as ((b & m) & Hbm & Hr). cbn [fst snd] in Hr.
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR0 Hbm) as (_ & Hb4096 & Hbce & Hbapp & _).
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a)
      by (unfold in_app, kLowShadowBeg, SHADOW_OFF in *; lia).
    refine (conj _ (conj (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR0 Hbm Hr) Ha64)).
    rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms)) (ms_mem ms) a
                 (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc Ha64 Happ)).
    rewrite <- (aview_at tfibsegs (w_H W) (unpoison U mem) mem a
                 (unpoison_app B ly S U W mem md a HARU0 Ha64 Happ)).
    replace a with (b + (a - b)) by ring.
    exact (Kblk b m (a - b) Hbm ltac:(lia)). }
assert (AG : pske_agree W W mem (ms_mem ms) (fun a => ~ psg1_KP (spZ regs) (ablocks B ly S) a)).
{ split.
  - intros a Ha Hn. apply (psg1_nn _ _ (psg1_kp_dec (spZ regs) (ablocks B ly S) a)); [|exact Hn].
    intros Hk. destruct (KEEP a Hk) as (Ev & Hni & _). exact (proj1 (psg1_view_pt _ _ _ a Ha Hni Ev)).
  - intros a Ha Hn Hp. apply (psg1_nn _ _ (psg1_kp_dec (spZ regs) (ablocks B ly S) a)); [|exact Hn].
    intros Hk. destruct (KEEP a Hk) as (Ev & Hni & _). exact (proj2 (psg1_view_pt _ _ _ a Ha Hni Ev) Hp). }
(* the window [entry sp, ot) stays present *)
assert (HNW : forall a, spZ regs <= a < ot -> ~ (fun a => ~ psg1_KP (spZ regs) (ablocks B ly S) a) a)
  by (intros a Ha Hn; apply Hn; left; lia).
pose proof (pske_present_window W W mem (ms_mem ms) _ regs ot AG ltac:(lia) HNW HPRESENT) as PRc.
assert (PRu : forall a, spZ regs <= a < ot -> apresent (w_H W) (unpoison U (ms_mem ms)) a).
{ intros a Ha. destruct (PRc a Ha) as (Hh & bb & Hb). split; [exact Hh|]. exists bb.
  rewrite (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc ltac:(lia) ltac:(right; lia)). exact Hb. }
(* ---- the journal at the raised window top ot ---- *)
pose proof (ps_aj_raise B STK_put_string (spZ regs) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) ly S W
  (unpoison U mem) md [(0, pos)] ly S2 W (unpoison U (ms_mem ms)) _ 0 HJ ltac:(lia) Hot16 Hottop PRu) as HJr.
(* ---- put's premises at the call ---- *)
assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms))).
{ intros a Hro Ho He. pose proof (fsw_roP_img a Hro) as Hi. pose proof (fs_segs_img a Hi) as Hl.
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold FS_IMG_END in Hl; lia).
  assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold FS_IMG_END, SHADOW_OFF in *; lia).
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms)) (ms_mem ms) a
               (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc Ha64 Happ)).
  rewrite (Kimg a Hi Ho He).
  rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a (unpoison_app B ly S U W mem md a HARU0 Ha64 Happ)).
  exact (HRO a Hro Ho He). }
destruct (ps_quote_src B HIMG ly S2 U W (ms_mem ms) _ buf HARUc HROc) as (HZq & HSq & HQ0 & HQce).
assert (HOUTc : FSH_Fn_writer.wout_ok B tfibsegs ly S2 W (ms_mem ms) o buf cap failed text).
{ apply (pske_wout_ok B ly S ly S2 W W mem (ms_mem ms) _ o buf cap failed text AG (Z.le_refl _)).
  - lia.
  - intros a Ha Hn. apply Hn. left. lia.
  - intros Hc. pose proof (Hbufblk Hc) as Hb.
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HAR0 Hb) as (_ & Hb4 & Hbce & _).
    pose proof (pss_req_ge (cap + HEAD)) as Hrq.
    split; [unfold HEAD in *; lia|]. split; [unfold HEAD in *; lia|].
    intros a Ha Hn. apply Hn. right. apply Exists_exists. exists (buf - HEAD, cap + HEAD).
    split; [exact Hb | cbn [fst snd]; unfold HEAD in *; lia].
  - intros Hb. rewrite Hab. exact Hb.
  - exact HOUT. }
assert (HGLOBc : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail).
{ apply (psg1_glob_keep W W mem (ms_mem ms)); [|exact HGLOB].
  intros a HP. pose proof (pss_pstat_img a HP) as Hi. pose proof (fs_segs_img a Hi) as Hl.
  destruct (proj1 HIMG a HP) as (Ho & He).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold FS_IMG_END in Hl; lia).
  assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold FS_IMG_END, SHADOW_OFF in *; lia).
  apply psg1_mbyte_of_aview.
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms)) (ms_mem ms) a
               (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc Ha64 Happ)).
  rewrite (Kimg a Hi Ho He).
  exact (aview_at tfibsegs (w_H W) (unpoison U mem) mem a (unpoison_app B ly S U W mem md a HARU0 Ha64 Happ)). }
(* the two saved words the chain reads, on the unpoisoned memory *)
destruct (ps_saved_words E0 (w_H W) (ms_mem ms) (spZ regs) (raZ regs) (s0Z regs) R8ok U8 Ux0 Ux1
  ltac:(unfold raZ; apply u64_range) ltac:(unfold s0Z; apply u64_range)) as (SW8 & SW16).
assert (UNP : forall a, spZ regs - 16 <= a < spZ regs ->
  aview tfibsegs (w_H W) (unpoison U (ms_mem ms)) a = aview tfibsegs (w_H W) (ms_mem ms) a).
{ intros a Ha. apply aview_at. apply (unpoison_app B ly S2 U W (ms_mem ms) _ a HARUc); [lia | right; lia]. }
assert (SW8u : rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (spZ regs - 8) = Some (raZ regs)).
{ rewrite (rdword_ext (aview tfibsegs (w_H W) (ms_mem ms)) _ (spZ regs - 8)); [exact SW8|].
  intros k Hk. apply UNP. lia. }
assert (SW16u : rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (spZ regs - 16) = Some (s0Z regs)).
{ rewrite (rdword_ext (aview tfibsegs (w_H W) (ms_mem ms)) _ (spZ regs - 16)); [exact SW16|].
  intros k Hk. apply UNP. lia. }
assert (HCH1 : achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (spZ (ms_regs ms)) (s0Z (ms_regs ms))
                 (ps_ch1 ly regs ch)).
{ rewrite Usp, Us0. exact (ps_chain_put B ly S U W regs mem md ch _ sp1 HPREa HAGU SW8u SW16u ltac:(lia)). }
assert (HCHc : o = spZ (ms_regs ms) + 8 /\ raZ (ms_regs ms) < alloc_ceiling \/
  spZ (ms_regs ms) + 16 <= o /\ exists ra nfp,
    rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (o - 8) = Some ra /\
    rdword (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (o - 16) = Some nfp /\
    (ra < 4096 \/ nfp < alloc_ceiling)).
{ right. rewrite Usp. split; [lia|].
  destruct Hchain as [(Eo & Hraa) | (Ho16 & ra & nfp & Hr8 & Hr16 & Hor)].
  - destruct (psg1_rdword_some (aview tfibsegs (w_H W) (unpoison U (ms_mem ms))) (o - 8)) as (ra & Hra).
    { intros k Hk. apply (aview_some_of_apresent tfibsegs). apply PRu. lia. }
    exists ra, (raZ regs). split; [exact Hra|]. split; [|right; exact Hraa].
    replace (o - 16) with (spZ regs - 8) by lia. exact SW8u.
  - exists ra, nfp. split; [|split; [|exact Hor]].
    + rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U mem)) _ (o - 8)); [exact Hr8|].
      intros k Hk. apply HAGU. lia.
    + rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U mem)) _ (o - 16)); [exact Hr16|].
      intros k Hk. apply HAGU. lia. }
clear Hchain.
assert (HPRc2 : forall a, spZ (ms_regs ms) <= a < ot -> apresent (w_H W) (ms_mem ms) a).
{ intros a Ha. rewrite Usp in Ha.
  destruct (Z_lt_le_dec a (spZ regs)) as [Hlt | Hge].
  - apply (fsw_apresent_unpoison B ly S2 U W (ms_mem ms) _ a HARUc); [lia|]. apply J14. lia.
  - exact (PRc a ltac:(lia)). }
assert (HFPR : forall a, inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a ->
  (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a /\
     exists b n, In (b, n) (ablocks B ly S2) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly S2) a \/
  (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a /\ in_img tfibsegs a) \/
  in_frames ly [(0, pos)] a).
{ intros a Ha. pose proof Ha as (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
  - right; right; left. split; [exact Ha | exact (pss_pstat_img a (ex_intro _ r (conj Hr Hra)))].
  - left. split; [exact Ha|]. unfold FSH_Fn_writer.wbuf_fp in Hr.
    destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [destruct Hr|].
    destruct Hr as [<- | []]. cbn [fst snd] in Hra.
    exists (buf - HEAD), (cap + HEAD). split; [rewrite Hab; exact (Hbufblk Ec) | exact (pss_wbuf_in buf cap a Hra)]. }
assert (Hbp1 : FSH_Fn_writer.wbudget_pre S2 cap cnt live
                 (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34])).
{ exact (psm_wbudget_pre1 S S2 failed text cap cnt fail live bs _ _ _ Hplain Hcap0 eq_refl eq_refl eq_refl Hbp
    ltac:(rewrite Hnev; lia) ltac:(rewrite Hbb; lia)). }
assert (Hretc : YK0s.ret_ok (YK11.getr (ms_regs ms) 1%bv)).
{ rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by (unfold PS_OPEN_RET; lia). reflexivity. }
assert (Hcs : forall regs' : bvmap 5 word,
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos) ++
                                               [Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))]))
            (mrestrict (w_H W) (ms_mem ms)) (spZ regs)) ps_sv_chunks).
{ intros r'. apply (psg1_sv_env E0); [|exact C8]. intros k Hk.
  unfold E0. rewrite ew_ewset_other by (unfold xatom; lia). rewrite !ps_ew_x.
  rewrite app_assoc. apply app_nth1. cbn. lia. }
assert (HCB : Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) ps_sv_chunks).
{ apply Forall_forall. intros c Hc. unfold ps_sv_chunks in Hc. apply in_map_iff in Hc as (k & <- & Hk).
  apply in_seq in Hk. cbn. lia. }
(* ---- the call: put's contract, and the kit's raised-top resume ---- *)
refine (ps_put_call B HPUT (STK_put_string + (ot - spZ regs)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
  [(0, pos)] ly S U U W mem md W ly S2 (ms_mem ms) (with_vm_backing (m_vm_lazy md2) mat md2) 0 (ms_regs ms)
  (sp1 - ot) (ps_ch1 ly regs ch) pos PS_OPEN_RET o PS_Q1 1 buf cap failed text [34] live peak cnt fail ot
  (spZ regs) (-104) 0 ps_sv_chunks
  (fs_extraT ++ ps_xs regs (flag_addr ly 0 pos) ++ [Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))]) Q
  HJr HARUc HROc ltac:(rewrite Usp; lia) (psg1_mod16 sp1 ot Hsp1m Hot16) ltac:(lia) ltac:(rewrite FSP, FS; lia)
  Hretc ltac:(rewrite Ura; unfold PS_OPEN_RET; lia) (eq_trans R3 Hgp0) (eq_trans R4 Htp0) HCH1
  (ps_heads B ly S ly S2 U Hab Hheads) ltac:(rewrite Hfrs; exact (ps_frames_callee (0, pos) (frames S) Hfr))
  R10 R11 R12 HOUTc HGLOBc HHEAD ltac:(rewrite Usp; lia) Hoot Hot16 Hottop HCHc HPRc2 HZq HSq eq_refl
  ltac:(constructor; [lia | constructor]) (conj HQ0 HQce) ltac:(left; unfold PS_Q1; lia)
  (psg1_wmax1 text bs Hplain Hwmax) Hcap Hlive Hbp1 R1
  (fun r' HP' => eq_trans (HP' 8 ltac:(unfold acallee_saved; lia)) R8)
  Hal16 ltac:(lia) ltac:(rewrite FS; lia) ltac:(lia) ltac:(lia) ltac:(rewrite FS, FSP, Usp; lia) ltac:(lia)
  ltac:(rewrite Usp; lia) ltac:(vm_compute; reflexivity) HCB Hcs ltac:(rewrite Usp; lia) ltac:(lia)
  ltac:(left; lia) HFPR Hin2
  (fun a Ha => pss_fr_off_fp B ly S2 W (unpoison U (ms_mem ms)) _ 0 pos buf cap a (ms_mem ms) o failed text
                 HARc Hin2 (Z.le_refl 0) HOUTc Ha) _).
intros st' buf' U' ly' S' W' regs' mem' md' Hst Hsw HJ' HARU' HPr HOUT' HBK HBS HKEEP HPK HSRC HFRK HS'.
subst st'. rewrite Z.add_0_l in HJ'. rewrite Usp in HKEEP. clear HSRC.
(* ---- the return state ---- *)
pose proof HJ' as (HAR' & Hly' & _ & _ & _ & Hfrs' & _ & _ & _ & _ & _ & _ & _ & J14' & _).
destruct (psg1_ly_addr _ ly ly' 0 pos Hly') as (EF' & EFL' & Etop').
assert (Hin' : In (0, pos) (frames S')) by (rewrite Hfrs'; left; reflexivity).
pose proof HARU' as (_ & OK' & PO').
assert (P2 : YK11.getr regs' 2%bv = YK11.getr (ms_regs ms) 2%bv) by exact (HPr 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs' 3%bv = YK11.getr (ms_regs ms) 3%bv) by exact (HPr 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs' 4%bv = YK11.getr (ms_regs ms) 4%bv) by exact (HPr 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs' 8%bv = YK11.getr (ms_regs ms) 8%bv) by exact (HPr 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs' 9%bv = YK11.getr (ms_regs ms) 9%bv) by exact (HPr 9 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs' 19%bv = YK11.getr (ms_regs ms) 19%bv)
  by exact (HPr 19 ltac:(unfold acallee_saved; lia)).
assert (P21 : YK11.getr regs' 21%bv = YK11.getr (ms_regs ms) 21%bv)
  by exact (HPr 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : YK11.getr regs' 22%bv = YK11.getr (ms_regs ms) 22%bv)
  by exact (HPr 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : YK11.getr regs' 23%bv = YK11.getr (ms_regs ms) 23%bv)
  by exact (HPr 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : YK11.getr regs' 24%bv = YK11.getr (ms_regs ms) 24%bv)
  by exact (HPr 24 ltac:(unfold acallee_saved; lia)).
assert (P18 : YK11.getr regs' 18%bv = YK11.getr (ms_regs ms) 18%bv)
  by exact (HPr 18 ltac:(unfold acallee_saved; lia)).
set (Xr := fs_extraT ++ ps_xs regs (flag_addr ly 0 pos) ++ [Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))]) in *.
assert (V8 : bv_unsigned (ew (Ereg regs' Xr) 8) = spZ regs).
{ rewrite (ew_Ereg_nat regs' Xr 8 8%bv eq_refl), P8, R8. apply wz. unfold spZ. apply u64_range. }
assert (V9 : bv_unsigned (ew (Ereg regs' Xr) 9) = sp1)
  by (rewrite (ew_Ereg_nat regs' Xr 9 9%bv eq_refl), P9, R9; apply wz; lia).
assert (V24 : bv_unsigned (ew (Ereg regs' Xr) 24) = frame_addr ly 0 pos)
  by (rewrite (ew_Ereg_nat regs' Xr 24 24%bv eq_refl), P24, R24; apply wz; lia).
assert (V18 : bv_unsigned (ew (Ereg regs' Xr) 18) = s)
  by (rewrite (ew_Ereg_nat regs' Xr 18 18%bv eq_refl), P18, R18; apply wz; lia).
assert (V47 : bv_unsigned (ew (Ereg regs' Xr) 47) = shadow_addr (frame_addr ly 0 pos)).
{ unfold Xr. change 47%nat with (32 + 15)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT ps_xs app].
  apply wz. lia. }
assert (V46 : bv_unsigned (ew (Ereg regs' Xr) (xatom 13)) = flag_addr ly 0 pos).
{ destruct (al_flag _ _ LAWS ly S2 W (unpoison U (ms_mem ms)) _ 0 pos HARc Hin2) as (_ & _ & Hflapp & Hflc).
  unfold Xr. rewrite ps_ew_x. cbn [nth fs_extraT ps_xs app]. apply wz. unfold in_app in Hflapp. lia. }
(* the blocks of the entry that are not the buffer's are still live at the return *)
pose proof HBS as HBS'. rewrite Hab in HBS'.
assert (KEEPB : forall p n, In (p, n) (ablocks B ly S) -> p <> buf - HEAD -> In (p, n) (ablocks B ly' S'))
  by (intros p n Hp Hne; exact (pss_bswap_keep _ _ _ _ _ _ _ _ HBS' Hp Hne)).
(* ---- the string region at the return: apart from the five fixed regions ---- *)
assert (D24 : s + (Z.of_nat (length bs) + 1) <= frame_addr ly 0 pos \/ frame_addr ly 0 pos + 64 <= s).
{ apply psg1_disj_pt; [lia | lia |]. intros x Hx.
  destruct (pss_str_off_fr B ly S U W mem buf s bs ly' S' W' (unpoison U' mem') md' pos x Hcstr Hsrck HAR' Hin'
    KEEPB ltac:(lia)) as (Hf & _). rewrite EF' in Hf. exact Hf. }
assert (D46 : s + (Z.of_nat (length bs) + 1) <= flag_addr ly 0 pos \/ flag_addr ly 0 pos + 1 <= s).
{ apply psg1_disj_pt; [lia | lia |]. intros x Hx Hfx.
  assert (EX : x = flag_addr ly' 0 pos) by (rewrite EFL'; lia).
  destruct (al_flag _ _ LAWS ly' S' W' (unpoison U' mem') md' 0 pos HAR' Hin') as (_ & Hown & _ & _).
  destruct (psg1_str_home ly S U W mem buf s bs ly' S' Hsrck KEEPB x ltac:(lia)) as [(p & k & Hpk & Hx') | Himg].
  - destruct (al_blocks _ _ LAWS ly' S' W' (unpoison U' mem') md' p k HAR' Hpk) as (_ & _ & _ & _ & Hbb' & _).
    apply (proj2 (Hbb' x Hx')). rewrite EX. exact Hown.
  - apply (proj2 (al_client_img _ _ LAWS ly' S' W' (unpoison U' mem') md' x HAR'
      (or_intror (or_intror (ex_intro _ 0 (ex_intro _ pos (conj Hin' EX))))))).
    exact Himg. }
pose proof (psg1_sh_str s (Z.of_nat (length bs)) (frame_addr ly 0 pos) alloc_ceiling Hamem ltac:(lia) HF4096 HFce
  ltac:(lia)) as D47.
(* ---- the frame's three chunk sets, on the memory after the call ---- *)
assert (MF : forall i, 0 <= i < 64 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') (frame_addr ly 0 pos + i) =
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (frame_addr ly 0 pos + i)).
{ intros i Hi. apply HFRK. left. change (fs_frame_bytes 0) with 64. lia. }
assert (MSH : forall i, 0 <= i < 8 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') (shadow_addr (frame_addr ly 0 pos) + i) =
  mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (shadow_addr (frame_addr ly 0 pos) + i)).
{ intros i Hi. apply HFRK. right. change (fs_frame_bytes 0 / 8) with 8. lia. }
assert (SLOT : Forall (YP09.chunk_ok tfibsegs (Ereg regs' Xr) (mrestrict (w_H W') mem') sp1) psj_scs0).
{ constructor; [|constructor].
  apply (ps_chunk_transfer E0 (Ereg regs' Xr) _ sp1 80 8 (SOff 10 0) (SOff 24 0)).
  - rewrite !fsw_SOff0. rewrite (ew_Ereg_nat regs' Xr 24 24%bv eq_refl), P24, R24.
    unfold E0. rewrite ew_ewset_other by discriminate. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact E10.
  - apply (psj_chunk_pt E0 (mrestrict (w_H W) (ms_mem ms))); [exact (Forall_inv C9)|].
    intros i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val cv_len Z.of_N] in Hi |- *.
    exact (proj1 (HKEEP (sp1 + 80 + i) ltac:(lia) ltac:(lia))). }
assert (HDR : Forall (YP09.chunk_ok tfibsegs (Ereg regs' Xr) (mrestrict (w_H W') mem') (frame_addr ly 0 pos))
                ps_hdr_chunks).
{ assert (MF8 : forall off, 0 <= off <= 56 -> forall i, 0 <= i < 8 ->
    mbyte tfibsegs (mrestrict (w_H W') mem') (frame_addr ly 0 pos + off + i) =
    mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (frame_addr ly 0 pos + off + i)).
  { intros off Hoff i Hi. rewrite <- Z.add_assoc. apply MF. lia. }
  unfold ps_hdr_chunks. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  - apply (psj_chunk_lit_pt E0 (Ereg regs' Xr) (mrestrict (w_H W) (ms_mem ms))).
    + apply (proj1 (Forall_forall _ _) C10). cbn [In]. repeat (first [left; reflexivity | right]).
    + intros i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val cv_len Z.of_N] in Hi |- *. apply MF8; lia.
  - apply (psj_chunk_lit_pt E0 (Ereg regs' Xr) (mrestrict (w_H W) (ms_mem ms))).
    + apply (proj1 (Forall_forall _ _) C10). cbn [In]. repeat (first [left; reflexivity | right]).
    + intros i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val cv_len Z.of_N] in Hi |- *. apply MF8; lia.
  - apply (psj_chunk_lit_pt E0 (Ereg regs' Xr) (mrestrict (w_H W) (ms_mem ms))).
    + apply (proj1 (Forall_forall _ _) C10). cbn [In]. repeat (first [left; reflexivity | right]).
    + intros i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val cv_len Z.of_N] in Hi |- *. apply MF8; lia.
  - apply (ps_chunk_transfer E0 (Ereg regs' Xr) _ _ 56 8 (SOff (xatom 13) 0) (SOff (xatom 13) 0)).
    + rewrite !fsw_SOff0. unfold E0. rewrite ew_ewset_other by (unfold xatom; discriminate).
      rewrite !ps_ew_x. unfold Xr. cbn [nth fs_extraT ps_xs app]. reflexivity.
    + apply (psj_chunk_pt E0 (mrestrict (w_H W) (ms_mem ms))).
      * apply (proj1 (Forall_forall _ _) C10). cbn [In]. repeat (first [left; reflexivity | right]).
      * intros i Hi. cbn [YP09.c_len YP09.c_off YP09.c_val cv_len Z.of_N] in Hi |- *. apply MF8; lia. }
assert (FSH : Forall (YP09.chunk_ok tfibsegs (Ereg regs' Xr) (mrestrict (w_H W') mem')
                        (shadow_addr (frame_addr ly 0 pos))) ps_fsh_chunks).
{ unfold ps_fsh_chunks.
  constructor; [psg1_sh C47 MSH 0 18446744073709551601 241|].
  constructor; [psg1_sh C47 MSH 1 18446744073709551601 241|].
  constructor; [psg1_sh C47 MSH 2 18446744073709551601 241|].
  constructor; [psg1_sh C47 MSH 3 18446744073709551601 241|].
  constructor; [psg1_sh C47 MSH 4 18446744073709551608 248|].
  constructor; [psg1_sh C47 MSH 5 18446744073709551603 243|].
  constructor; [psg1_sh C47 MSH 6 18446744073709551603 243|].
  constructor; [psg1_sh C47 MSH 7 18446744073709551603 243|].
  constructor. }
(* ---- the return shape ps_ret_ss PS_OPEN_RET L psj_scs0 [the string] ---- *)
assert (HST : st_ok tfibsegs (Ereg regs' Xr)
  (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 PS_OPEN_RET) mem' (seg_rom tfibsegs)))).
{ apply (psr_resume B (STK_put_string + (ot - spZ regs)) ot (spZ regs) (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
    ly S W (unpoison U mem) md [(0, pos)] ly' S' U' W' mem' md' _ regs' regs PS_OPEN_RET (Z.of_nat (length bs)) pos
    (frame_addr ly 0 pos) (flag_addr ly 0 pos) sp1 s psj_scs0 [ps_str_region (Z.of_nat (length bs))]
    HS' HJ' HARU' Hin' (eq_sym EF') (eq_sym EFL') (eq_trans P8 R8) (eq_trans P9 R9) (eq_trans P21 R21)
    (eq_trans P22 R22) (eq_trans P23 R23) (eq_trans P24 R24) (eq_trans P18 R18)
    ltac:(rewrite FS; lia) ltac:(lia) ltac:(lia) Hsp1m ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
    SLOT HDR FSH (psg1_regwf_str (Z.of_nat (length bs)) ltac:(lia))
    (psg1_str_ok (Ereg regs' Xr) (mrestrict (w_H W') mem') s (Z.of_nat (length bs)) V18 ltac:(lia) ltac:(lia))).
  - exact (psg1_dj_str (Ereg regs' Xr) psj_scs0 (spZ regs) sp1 (frame_addr ly 0 pos) (flag_addr ly 0 pos) s
      (Z.of_nat (length bs)) V8 V9 V24 V47 V46 V18 ltac:(lia) ltac:(lia) D24 D47 D46).
  - exact (conj I I). }
(* ---- fs_heads and the buffer head at the return (ZZpsg1k), then the string (ZZpsg3k) ---- *)
destruct (ps_heads_put B ly S2 U W (ms_mem ms) _ ly' S' U' W' mem' md' o buf buf' cap _ _ _
  HARUc (ps_heads B ly S ly S2 U Hab Hheads) Hcb0 HHEAD HARU' HOUT' HBS Hsw) as (HH' & HHD').
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
{ apply (arodata_kept_own B _ _ _ ly S U W mem md [(0, pos)] ly' S' U' W' mem' md' _ HJ' HARU0 OK' PO').
  - intros (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
    + pose proof (pss_pstat_rng 0 (ex_intro _ r (conj Hr Hra))) as (H1 & _). lia.
    + unfold FSH_Fn_writer.wbuf_fp in Hr. destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HAR0 (Hbufblk Ec)) as (_ & Hb4 & _).
      lia.
  - intros a Hro (r & Hr & Hra). apply in_app_or in Hr as [Hr | Hr].
    + exact (psg1_pstat_not_ro a (ex_intro _ r (conj Hr Hra)) Hro).
    + unfold FSH_Fn_writer.wbuf_fp in Hr. destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [destruct Hr|].
      destruct Hr as [<- | []]. cbn [fst snd] in Hra.
      exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ a HAR0 (Hbufblk Ec)
               (pss_wbuf_in buf cap a Hra) (fsw_roP_img a Hro)).
  - exact HRO. }
destruct (ps_str_keep B HIMG (STK_put_string + (ot - spZ regs)) ot ly S U W mem md [(0, pos)] ly' S' U' W' mem' md'
  _ buf cap buf' _ s bs HARU0 HRO HJ' HARU' HH' HRO' HBS' Hsw Hbufblk Hcstr Hsrck) as (Hcstr' & Hsrck').
(* ---- ps_inv ---- *)
apply (KONT pos ly ly' S' U' W' regs' mem' md' buf').
unfold ps_inv. cbv zeta.
injection HIDE as Esp1. rewrite <- Esp1.
split; [exact Hin'|]. split; [exact Hfrs'|]. split; [reflexivity|].
split; [exact HJ'|]. split; [exact HARU'|].
split; [exact HST|]. split; [reflexivity|].
split; [exact (eq_trans P2 R2)|]. split; [exact (eq_trans P8 R8)|]. split; [exact (eq_trans P9 R9)|].
split; [exact (eq_trans P19 R19)|]. split; [exact (eq_trans P21 R21)|]. split; [exact (eq_trans P22 R22)|].
split; [exact (eq_trans P23 R23)|]. split; [exact (eq_trans P24 R24)|]. split; [exact (eq_trans P18 R18)|].
split; [exact (eq_trans P3 R3)|]. split; [exact (eq_trans P4 R4)|].
split; [exact (Forall_inv SLOT)|]. split; [exact HDR|]. split; [exact FSH|].
split; [exact Hsw|]. split; [exact HOUT'|].
split; [destruct HBK as (K1 & K2 & K3); rewrite Hbb in K2; exact (conj K1 (conj K2 K3))|].
split; [exact HBS'|].
split.
{ intros a Ha Ho.
  destruct (HKEEP a ltac:(lia) Ho) as (Hm1 & Hw1).
  assert (Hn : ~ (fun a => ~ psg1_KP (spZ regs) (ablocks B ly S) a) a) by (intros Hn; apply Hn; left; lia).
  assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
  assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (fs_segs_img a Hi); unfold FS_IMG_END in *; lia).
  split.
  - rewrite Hm1. exact (pske_mbyte W W mem (ms_mem ms) _ a AG Ha64 Hn).
  - exact (iff_trans (pske_writable W W mem (ms_mem ms) _ a AG Ha64 Hn
             (or_intror (seg_rom_none tfibsegs a Ha64 Hni))) Hw1). }
split; [exact Hcstr'|]. split; [exact HPK|]. split; [exact Hsrck'|].
split; [exact HHD'|]. split; [exact HH'|]. split; [exact HRO'|].
intros a Ha. apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' a HARU'); [lia|].
apply J14'. rewrite FS. lia.
Qed.

(* psg1 is SEG1 of ps_close VERBATIM: its type is checked against ps_close's first premise, read off ps_close *)
Definition psg1_fits := ps_close B psg1.

End G.
