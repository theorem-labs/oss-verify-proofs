(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 134 of its 204 lines of code are new or changed and 861 lines of the source are left out. *)
(* The image-free part of the seat of a phase of pcap_source_next (lib/A/Prog/PcapSourceNextSeat.v):
   the walk's atoms, the chunk and region constructors, the shadow entry, the atom facts, and the
   lemmas that speak of no image. The ASan build's seat (lib/A/Prog/PcapSourceNextSeat.v) and the
   asan-ubsan build's (lib/B/Prog/PcapSourceNextSeat.v) both Require this file, so the two images
   share ONE set of constants: a chunk list built here is the same term in both, which is what the
   walk engine's `vm_compute` comparisons need.

   The rule this file exists for (porter 01:25Z): the Require closure of a lib/B file may hold only
   lib/B files, the shared core, and image-free lib/A files. So nothing here may name an image-A
   table or instance (PcapPa / PcapPaLib / PcapList / PcapAddr / PcapSyms / PcapFrame / YC1g / YC1h)
   or an image-A address; the numbers it does use (NX_MAGIC, NX_FRAME, PS_LEN, the PS_* offsets,
   nx_bufn) come from the image-free statement file lib/A/Prog/PcapSourceNextSpec.v, where the two
   builds share them (same source, same struct, same frame class).

   What stays in each build's own seat: the spill chunks and the spill region (the slots differ with
   the machine frame's size), the region list nx_regions / nx_ss and nx_land_chk (they name the
   image's GOT word and shadow-base cell), the symbolic registers nx_sr, and every lemma over an
   image's `PAImg` instance (nx_seat, nx_land, the region_ok and disjointness lemmas, the kept
   step). Their names are unchanged in both. The two files that Require this one are
   lib/A/Prog/PcapSourceNextSeat.v and lib/B/Prog/PcapSourceNextSeat.v. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the atoms of this walk ---- *)
Definition NA_SP : nat := 2%nat.     (* the caller's stack pointer, the entry x2   *)
Definition NA_PS : nat := 10%nat.    (* ps, the entry a0                           *)
Definition NA_BUF : nat := 11%nat.   (* buf, the entry a1                          *)
Definition NA_TS : nat := 13%nat.    (* &ts, the entry a3                          *)
Definition NA_SB : nat := 32%nat.    (* SHADOW_OFF                                 *)
Definition NA_SP1 : nat := 60%nat.   (* the realigned stack pointer, s1            *)
Definition NA_F : nat := 516%nat.    (* the frame on the side stack                *)
Definition NA_FL : nat := 528%nat.   (* its flag word                              *)
Definition NA_FSH : nat := 529%nat.  (* its shadow bytes                           *)
(* The current registers of a phase's first seat (nx_mkE, nx_sr): x_i is the atom NA_CUR + i. *)
Definition NA_CUR : nat := 530%nat.

(* The shadow base as the token engine sees it, and the shadow address of x. *)
Definition nx_Bx : sv := SOff NA_SB 0.
Definition nx_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) nx_Bx.

(* ---- the chunks ---- *)

(* The saved words of the machine frame: ra at the caller's sp - 8, then s0, s1, s2 .. s11 at
   sp - 16 - 8j (0x81824..0x81854), the registers x8, x9, x18 .. x27. *)
Definition nx_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1%nat 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8%nat 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9%nat 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18%nat 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19%nat 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 20%nat 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21%nat 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 22%nat 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23%nat 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24%nat 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25%nat 0));
    YP09.mkChunk (-96) (CVal 8 (SOff 26%nat 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27%nat 0)) ].

(* The frame's header (0x818ec..0x818f4): the live magic and the listing's objects 13 and 14. *)
Definition nx_hdr_chunks : list YP09.chunk :=
  [ YP09.mkChunk 0 (CVal 8 (SLit NX_MAGIC));
    YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 13) 0));
    YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 14) 0)) ].

Fixpoint nx_sh_chunks_from (i : Z) (sh : list Z) : list YP09.chunk :=
  match sh with
  | [] => []
  | v :: t => YP09.mkChunk i (CVal 1 (SLit v)) :: nx_sh_chunks_from (i + 1) t
  end.
(* The frame's shadow bytes as chunks, one per byte. *)
Definition nx_sh_chunks (sh : list Z) : list YP09.chunk := nx_sh_chunks_from 0 sh.

(* ---- the regions ---- *)

(* 0: the machine frame's saved words, read-only (the body never writes them). *)
Definition nx_saved_region : YP09.region :=
  YP09.mkRegion (Some NA_SP) (-104) 0 0 0 nx_saved_chunks.
(* 2: the class-0 frame on the side stack, writable on [0, fw): the header, the phase's chunks fcs,
   and the flag pointer the slot keeps in its last word (F + 56, read at 0x81d68). *)
Definition nx_frame_region (fw : Z) (fcs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some NA_F) 0 NX_FRAME 0 fw
    (nx_hdr_chunks ++ fcs ++ [YP09.mkChunk (NX_FRAME - 8) (CVal 8 (SOff NA_FL 0))]).
(* 3: the frame's 8 shadow bytes, writable on [swlo, swhi). During a token run keep it read-only
   (swlo = swhi): the engine's static check (YCbn.v cells_safe_b) refuses a writable window in the
   shadow that no shadow entry covers. *)
Definition nx_shadow_region (swlo swhi : Z) (sh : list Z) : YP09.region :=
  YP09.mkRegion (Some NA_FSH) 0 8 swlo swhi (nx_sh_chunks sh).

(* The regions a phase may add in `extra`: the caller's struct (24 bytes at the entry a0),
   writable on [0, pw); the record buffer's first n bytes (n concrete: the engine compares offsets
   with r_hi), writable on [0, bw); the timestamp cell, writable on [0, tw). *)
Definition nx_ps_region (pw : Z) (pcs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some NA_PS) 0 PS_LEN 0 pw pcs.
Definition nx_buf_region (n bw : Z) (bcs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some NA_BUF) 0 n 0 bw bcs.
Definition nx_ts_region (tw : Z) (tcs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some NA_TS) 0 8 0 tw tcs.
(* The struct's fields as chunks, with the values the phase knows them by. *)
Definition nx_ps_chunks (eh esw eol evt evid : sv) (pd0 pd1 : Z) : list YP09.chunk :=
  [ YP09.mkChunk PS_F_OFF (CVal 8 eh); YP09.mkChunk PS_SW_OFF (CVal 4 esw);
    YP09.mkChunk PS_OL_OFF (CVal 4 eol); YP09.mkChunk PS_VT_OFF (CVal 4 evt);
    YP09.mkChunk PS_VID_OFF (CVal 2 evid);
    YP09.mkChunk 22 (CVal 1 (SLit pd0)); YP09.mkChunk 23 (CVal 1 (SLit pd1)) ].

(* The shadow entry of the caller's struct (its 24 bytes are addressable). *)
Definition nx_SH : list shent := [mkSHE NA_PS 0 PS_LEN].

(* The atom facts of the fixed part: the two stack pointers, ps, the shadow base, the frame, its
   flag and its shadow (nx_facts0_ok). *)
Definition nx_facts0 : facts :=
  mkFacts [ (NA_SP, mkAF (2 ^ 46) (2 ^ 47) 4); (NA_PS, mkAF 4096 (2 ^ 47 - 24) 3);
            (NA_SB, mkAF SHADOW_OFF SHADOW_OFF 0); (NA_SP1, mkAF (2 ^ 46) (2 ^ 47) 5);
            (NA_F, mkAF 4096 (2 ^ 47) 6); (NA_FL, mkAF 4096 (2 ^ 47) 0);
            (NA_FSH, mkAF SHADOW_OFF (2 ^ 47) 3) ] [] [].


(* ---- generic lemmas ---- *)

Lemma nx_all_disj_app : forall (E : env) r l1 l2,
  YP09.all_disjoint E r l1 -> YP09.all_disjoint E r l2 -> YP09.all_disjoint E r (l1 ++ l2).
Proof.
  intros E r l1. induction l1 as [|x l1 IH]; intros l2 H1 H2; cbn [app YP09.all_disjoint] in *;
    [exact H2|]. destruct H1 as [Hx Hr]. split; [exact Hx | exact (IH l2 Hr H2)].
Qed.

Lemma nx_pwd_app : forall (E : env) l1 l2,
  YP09.pairwise_disjoint E l1 -> YP09.pairwise_disjoint E l2 ->
  Forall (fun r => YP09.all_disjoint E r l2) l1 ->
  YP09.pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|r l1 IH]; intros l2 H1 H2 HF; cbn [app]; [exact H2|].
  cbn [YP09.pairwise_disjoint] in H1 |- *. destruct H1 as [Ha Hp].
  inversion HF as [|x y Hx Ht]; subst.
  split; [apply nx_all_disj_app; [exact Ha | exact Hx] | exact (IH l2 Hp H2 Ht)].
Qed.

Lemma nx_sh_chunks_from_In : forall sh i j, (i < length sh)%nat ->
  In (YP09.mkChunk (j + Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (nx_sh_chunks_from j sh).
Proof.
  intros sh. induction sh as [|v t IH]; intros i j Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [nx_sh_chunks_from nth].
  - left. rewrite Z.add_0_r. reflexivity.
  - right. replace (j + Z.of_nat (S i)) with (j + 1 + Z.of_nat i) by lia.
    apply IH. cbn [length] in Hi. lia.
Qed.

Lemma nx_sh_chunks_In : forall sh i, (i < length sh)%nat ->
  In (YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i sh 0)))) (nx_sh_chunks sh).
Proof.
  intros sh i Hi. unfold nx_sh_chunks.
  replace (Z.of_nat i) with (0 + Z.of_nat i) by lia. apply nx_sh_chunks_from_In. exact Hi.
Qed.

Lemma nx_sv_SOff0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* Disjointness against a longer extra list, one region at a time. *)
Lemma nx_fix_disj_cons : forall (E : env) rs x l,
  Forall (fun r => YP09.all_disjoint E r [x]) rs -> Forall (fun r => YP09.all_disjoint E r l) rs ->
  Forall (fun r => YP09.all_disjoint E r (x :: l)) rs.
Proof.
  intros E rs x l H1 H2. induction rs as [|r rs IH]; [constructor|].
  inversion H1 as [|? ? [Hx _] H1']; subst. inversion H2 as [|? ? Hl H2']; subst.
  constructor; [split; [exact Hx | exact Hl] | exact (IH H1' H2')].
Qed.


(* ---- landing from any region list that still holds the fixed part's chunks ---- *)
(* A walk may reorder a region's chunks or store new literals into the frame's shadow; nx_land0_by
   needs only that each chunk is still in some region of the right base (checked by computation). *)
Definition nx_cval_eqb (a b : cval) : bool :=
  match a, b with CVal w v, CVal w' v' => N.eqb w w' && sv_eqb v v' | _, _ => false end.
Definition nx_chunk_eqb (a b : YP09.chunk) : bool :=
  Z.eqb (YP09.c_off a) (YP09.c_off b) && nx_cval_eqb (YP09.c_val a) (YP09.c_val b).
Lemma nx_chunk_eqb_eq : forall a b, nx_chunk_eqb a b = true -> a = b.
Proof.
  intros [oa va] [ob vb] H. unfold nx_chunk_eqb in H. cbn [YP09.c_off YP09.c_val] in H.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst ob.
  destruct va as [w v| | |]; destruct vb as [w' v'| | |]; cbn in H2; try discriminate.
  apply andb_prop in H2 as [H3 H4]. apply N.eqb_eq in H3. apply sv_eqb_eq in H4. subst. reflexivity.
Qed.
Definition nx_hasb (rs : YP09.smem) (n : nat) (c : YP09.chunk) : bool :=
  existsb (fun r => YP09.obase_eqb (YP09.r_base r) (Some n) && existsb (nx_chunk_eqb c) (YP09.r_chunks r)) rs.
Lemma nx_hasb_sound : forall rs n c, nx_hasb rs n c = true ->
  exists lo hi wlo whi cs, In (YP09.mkRegion (Some n) lo hi wlo whi cs) rs /\ In c cs.
Proof.
  intros rs n c H. unfold nx_hasb in H. apply existsb_exists in H as ([b lo hi wlo whi cs] & Hin & Hr).
  cbn [YP09.r_base YP09.r_chunks] in Hr. apply andb_prop in Hr as [Hb Hc].
  apply YP09.obase_eqb_eq in Hb. subst b. apply existsb_exists in Hc as (c' & Hc' & Heq).
  apply nx_chunk_eqb_eq in Heq. subst c'. exists lo, hi, wlo, whi, cs. split; assumption.
Qed.

Lemma nx_div8_64 : forall a, a mod 64 = 0 -> a / 8 = 8 * (a / 64) /\ a = 64 * (a / 64).
Proof.
  intros a H. pose proof (Z_div_mod_eq_full a 64) as E. rewrite H, Z.add_0_r in E. split; [|exact E].
  symmetry. apply (Z.div_unique a 8 (8 * (a / 64)) 0); [left; lia | lia].
Qed.

Lemma nx_bufn_le : forall c, c <= nx_bufn c /\ 1 <= nx_bufn c.
Proof. intros c. unfold nx_bufn. lia. Qed.


(* ---- lemmas over any image (the lib/B twin reuses them) ---- *)
Section g0.
Context {segs : list Segment}.
Lemma nx_rdword_range : forall H mem a v, rdword (aview segs H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H mem a v Hr. unfold rdword in Hr.
  assert (Hb : forall x b, aview segs H mem x = Some b -> 0 <= b < 256).
  { intros x b Hx. unfold aview in Hx.
    destruct (YP09.mbyte segs (mrestrict H mem) x) as [y|]; cbn [option_map] in Hx; [|discriminate].
    injection Hx as <-. pose proof (bv_unsigned_in_range 8 y) as Hy.
    change (bv_modulus 8) with 256 in Hy. lia. }
  destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
  destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
  destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
  destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
  destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
  destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
  destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
  destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
  injection Hr as <-.
  apply Hb in E0. apply Hb in E1. apply Hb in E2. apply Hb in E3.
  apply Hb in E4. apply Hb in E5. apply Hb in E6. apply Hb in E7. lia.
Qed.

Lemma nx_U_Bx : forall E, ew E NA_SB = w64 SHADOW_OFF -> U E nx_Bx = SHADOW_OFF.
Proof. intros E H. unfold nx_Bx. apply (U_atom E NA_SB SHADOW_OFF H). unfold SHADOW_OFF. lia. Qed.

Lemma nx_shent_ok : forall E m (n : nat) v lo hi,
  ew E NA_SB = w64 SHADOW_OFF -> ew E n = w64 v -> 0 <= v < 2 ^ 64 -> lo <= hi ->
  amem_range (v + lo) (hi - lo) ->
  range_addressable (rd_of segs m) SHADOW_OFF (v + lo) (hi - lo) ->
  shent_ok segs nx_Bx E m (mkSHE n lo hi).
Proof.
  intros E m n v lo hi HB Hn Hv Hlh Ham HR. unfold shent_ok, app_apart.
  cbn [she_m she_lo she_hi]. rewrite (nx_U_Bx E HB), (U_atom E n v Hn Hv). split; [exact HR|].
  intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma nx_U_shx : forall E n v c, ew E NA_SB = w64 SHADOW_OFF -> ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c -> v + c < 2 ^ 47 ->
  sv_denot E (nx_shx (SOff n c)) = Z_to_bv 64 (shadow_of_addr SHADOW_OFF (v + c)).
Proof.
  intros E n v c HB0 Hn Hv Hc0 Hc1. rewrite denot_lit_U. f_equal. unfold nx_shx.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (srl3_any_U E (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff n c) eq_refl).
  rewrite (U_atom_off E n v c Hn Hv) by lia. rewrite (nx_U_Bx E HB0).
  unfold shadow_of_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF.
  assert ((v + c) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= (v + c) / 8) by (apply Z.div_pos; lia). lia.
Qed.
End g0.

Section g1.
Context {val : nat -> Z} {lim : nat}.
Lemma nx_img_env_ewset : forall E n w, img_env val lim E -> (n < A_TEXT \/ lim <= n)%nat ->
  img_env val lim (ewset E n w).
Proof.
  intros E n w HE Hn a Ha. rewrite ew_ewset_other by (unfold A_TEXT in *; lia). exact (HE a Ha).
Qed.
End g1.
