(* The footprint twin of build_dt1_single.v (image A; RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF
   under a footprint RNG (build_dt1_single_contract_F), by the script of build_dt1_single.v over StepF's step. Each
   access of this image's own code is closed from one rng premise: the stores and loads of ra and s0 .. s3 in the
   48-byte frame (inside the window K below sp); the two 8-byte loads of the GOT cell 0x9fad0 and of the cell that
   holds the shadow offset (both inside [RT_LO, RT_HI)); the 1-byte stores of the 20 header bytes, of the record
   check byte, of the byte 247 and of the block check byte, and the 1-byte loads of the two sum loops, all inside
   the 32 bytes at o; and the 1-byte load of the shadow byte before each of those loads and stores. The run has one
   callee, __asan_memcpy (the copy of the n bytes at d to o + 20), and build_dt1_single.v's theorem takes its old
   contract as a hypothesis, so this twin takes its footprint form in the same place: a Theorem Labs lane's shared statement
   asan_memcpy_contract_F (lib/A/Prog/asan_memcpy_cF.v), which a Theorem Labs lane proves (asan_memcpy_holds_F in
   asan_memcpyF.v). build_dt1_single_holds_of_F re-derives the old contract from the footprint form
   (build_dt1_single_contract_of_F at RNG_all). build_dt1_single.v and its theorem are unchanged. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT RcAsanFPLib asan_memcpy_c
  asan_memcpy_cF build_dt1_single_c build_dt1_single.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* The callee proof, for the closed corollary at the end of this file.  Loaded without Import: its notations and
   tactics must not shadow the ones this proof's script is written against. *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The store hook of this file: StepF's mem_after_store_opt without norm_lit_store_bytes, which would rewrite the
   goal shape [write_to_mem mc A (le1 v)] that this file's store tactic astF and its rc_le1_* rewrites match.
   Everything else is StepF's hook, guard included. *)
Ltac bdaF_store_opt :=
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= bdaF_store_opt.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Z.div is opaque to lia, so the consequences of an 8-aligned shadow word cover are drawn here, each in a
   context with no other division: the shadow byte of one checked byte, and the cover of a sub-range (the shape
   __asan_memcpy's _F contract names), also from the shadow word span of the window. *)
Lemma bdaF_floor8 : forall y, y / 8 * 8 <= y <= y / 8 * 8 + 7.
Proof.
  intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.

Lemma bdaF_sh1 : forall RNG K a b x,
  rng RNG ((a / 8 + K) / 8 * 8) ((b / 8 + K) / 8 * 8 + 8 - (a / 8 + K) / 8 * 8) ->
  a <= x <= b -> rng RNG (x / 8 + K) 1.
Proof.
  intros RNG K a b x H Hx. eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono a x 8 ltac:(lia) ltac:(lia)). pose proof (bdaF_floor8 (a / 8 + K)). lia.
  - pose proof (Z.div_le_mono x b 8 ltac:(lia) ltac:(lia)). pose proof (bdaF_floor8 (b / 8 + K)). lia.
Qed.

Lemma bdaF_shK : forall RNG K a b u v,
  rng RNG ((a / 8 + K) / 8 * 8) ((b / 8 + K) / 8 * 8 + 8 - (a / 8 + K) / 8 * 8) ->
  a <= u -> u <= v -> v <= b ->
  rng RNG ((u / 8 + K) / 8 * 8) ((v / 8 + K) / 8 * 8 + 8 - (u / 8 + K) / 8 * 8).
Proof.
  intros RNG K a b u v H Hau Huv Hvb. eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono a u 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (a / 8 + K) (u / 8 + K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono v b 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (v / 8 + K) (b / 8 + K) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The 8-aligned shadow word span of a window [p, p + n), n > 0 (sh_word_rng of asan_memcpy_cF.v, the premise of
   build_dt1_single_contract_F), covers the cover of any sub-range: the frame of __asan_memcpy below sp - 48. *)
Lemma bdaF_wincov : forall RNG p n u v,
  sh_word_rng RNG p n -> 0 < n -> p <= u -> u <= v -> v <= p + n - 1 ->
  rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8).
Proof.
  intros RNG p n u v [E|H] Hn H1 H2 H3; [lia|].
  unfold sh_al8_lo, sh_al8_hi, shadow_addr in H.
  exact (bdaF_shK RNG ASAN_K p (p + n - 1) u v H H1 H2 H3).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The twin of build_dt1_single.v's Section BDA: the same variables and premises, the footprint form of the callee
   in place of its old contract, and the rng premises of the run. *)
Section BDAF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 J20 : list byte) (nn : nat) (off : Z)
    (RNG : footprint).
  Hypothesis HMC : asan_memcpy_contract_F.
  Hypothesis Rsp : 0 <= bv_unsigned sp < 2^64.
  Hypothesis Hsp : 2272 <= bv_unsigned sp.
  Hypothesis Ro : 0 <= bv_unsigned wo.
  Hypothesis Ho32 : bv_unsigned wo + 32 <= 2^64.
  Hypothesis Rd : 0 <= bv_unsigned wd.
  Hypothesis Hd : bv_unsigned wd + bv_unsigned wn <= 2^64.
  Hypothesis Hnn : Z.of_nat nn = bv_unsigned wn.
  Hypothesis Hn9 : (nn <= 9)%nat.
  Hypothesis HLD : length D = nn.
  Hypothesis Lob : length ob = 32%nat.
  Hypothesis LJ20 : length J20 = nn.
  Hypothesis EP5 : P5 = firstn (9 - nn) (skipn (22 + nn) ob).
  Hypothesis DfO : bv_unsigned sp <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned sp - 2272.
  Hypothesis DdO : bv_unsigned wd + bv_unsigned wn <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned wd.
  Hypothesis Dfd : bv_unsigned sp <= bv_unsigned wd \/ bv_unsigned wd + bv_unsigned wn <= bv_unsigned sp - 2272.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 2272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis HCE : asan_cells m.
  Hypothesis HSW : shadow_rw m.
  Hypothesis HADo : addressable m (bv_unsigned wo) 32.
  Hypothesis HADd : addressable m (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis HAPo : app_mem (bv_unsigned wo + 32).
  Hypothesis HEd : end_in_app (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis H7d : bv_unsigned wn = 0 \/ app_mem (bv_unsigned wd + 7).
  Hypothesis HRTo : bv_unsigned wo + 32 <= RT_LO \/ RT_HI <= bv_unsigned wo.

  (* The contract's footprint. *)
  Definition WaF : list ivl :=
    [(bv_unsigned sp + -2272, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  (* The shadow bytes of the 32 bytes at o, read in m, with the offset off that s3 holds. *)
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned wo) 32 WaF.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned wo) 32.

  (* The rng premises of build_dt1_single_contract_F: the image [IMG_LO, IMG_HI), which the callee's _F contract
     takes; the window K below sp (this 48-byte frame and the window of __asan_memcpy below it) and the 8-aligned
     shadow word span of that window, which holds the shadow of the callee's frame; the runtime words, which hold
     the GOT cell and the cell of the shadow offset; the 32 bytes at o and the n bytes at d; and the shadow bytes of
     those two ranges.
     The shadow premises are QUANTIFIED, and that is deliberate: `lia` unfolds `rng` (it is a transparent
     conjunction of bounds), so a ground premise whose bounds hold nested `/ 8` terms puts Euclidean variables into
     every `lia` call of the script below. Under a `forall`, zify skips the premise, and the run draws exactly the
     consequences it needs: one shadow byte per checked byte (RSo1, with the offset off that the run reads out of
     the runtime cell), and the 8-aligned shadow word cover of a sub-range (RSoK / RSdK / RWSK, with ASAN_K, the
     shape the callee's _F contract names). The caller discharges them from the aligned-cover premises of
     build_dt1_single_contract_F, where off is ASAN_K. *)
  (* The footprint is decided byte by byte: the callee's _F contract takes this. *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
  Hypothesis RWIN : rng RNG (bv_unsigned sp - 2272) 2272.
  Hypothesis RRT : rng RNG RT_LO (RT_HI - RT_LO).
  Hypothesis ROUT : rng RNG (bv_unsigned wo) 32.
  Hypothesis RDAT : rng RNG (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis RSo1 : forall x, bv_unsigned wo <= x <= bv_unsigned wo + 31 -> rng RNG (x / 8 + off) 1.
  Hypothesis RSoK : forall a b, bv_unsigned wo <= a -> a <= b -> b <= bv_unsigned wo + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis RSdK : forall a b, bv_unsigned wd <= a -> a <= b -> b <= bv_unsigned wd + bv_unsigned wn - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis RWSK : forall a b, bv_unsigned sp - 2272 <= a -> a <= b -> b <= bv_unsigned sp - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

  Definition QaF : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch WaF m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp)
      /\ asan_cells m' /\ shadow_rw m'.

  Definition fraF (m' : word -> option byte) : Prop :=
    exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma bdaF_so : forall x, in_shadow x -> outside WaF x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bda_shadow_out m (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HADo ltac:(lia)).
  Qed.

  Lemma bdaF_ro : forall x, RT_LO <= x < RT_HI -> outside WaF x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bda_rt_out (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HRTo ltac:(lia)).
  Qed.

  (* The runtime's cells and the shadow are outside WaF: a run that writes only WaF keeps them. *)
  Lemma bdaF_rt : forall m', munch WaF m m' -> wmono rsegs m m' -> asan_cells m' /\ shadow_rw m'.
  Proof.
    intros m' MU WM. split.
    - exact (fl_asan_cells WaF m m' HCE MU bdaF_ro).
    - exact (fl_shadow_rw WaF m m' HSW MU WM bdaF_so).
  Qed.

  Lemma bdaF_app_o : forall t, 0 <= t <= 32 -> app_mem (bv_unsigned wo + t).
  Proof.
    intros t Ht. apply bda_app_mid; [|exact HAPo|exact Ht].
    pose proof (bda_addr_app m _ 32 0 HADo ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
  Qed.

  (* The check of byte o + j in a memory m' that the run reached writing only WaF. *)
  Lemma bdaF_shadow : forall m' X j, munch WaF m m' -> 0 <= j < 32 -> X = bv_unsigned wo + j ->
    exists k : byte, ov_read_bytes rsegs m' (wa (X / 8 + off)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros m' X j MU Hj ->.
    pose proof (asan_shadow_rd_munch rsegs m m' off _ 32 WaF WaF HSR MU (fun x Hx => Hx)) as HR'.
    pose proof (asan_addressable_munch rsegs m m' off _ 32 WaF WaF HAD HSR MU (fun x Hx => Hx)) as HA'.
    destruct (asan_shadow_read rsegs m' off _ 32 WaF j HR' Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HA' j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A store of one byte at o + j, 0 <= j < 32, inside WaF. *)
  Lemma ostF : forall m' j (b : byte), 0 <= j < 32 -> inside WaF (bv_unsigned wo + j) 1 ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    fraF (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch WaF m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wmono rsegs m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    mem_inv rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    stk rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned sp + -2272) (bv_unsigned sp + -48) /\
    bytes_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo + j) [b].
  Proof.
    intros m' j b Hj Hin (jk & FR) WO MU WM MI ST.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 j 1 WO ltac:(lia) ltac:(lia)) as HS.
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
    apply bytes_at_write_same; cbn [length]; lia.
  Qed.

  (* The state of the header stores: P is the part of the header written so far. *)
  Definition ainvF (m' : word -> option byte) (P : list byte) : Prop :=
    fraF m' /\ wr_at rsegs m' (bv_unsigned wo) 32 /\ bytes_at rsegs m' (bv_unsigned wo) P /\
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 /\ bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 /\
    bytes_at rsegs m' (bv_unsigned wd) D /\
    munch WaF m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48).

  Lemma ainvF_mu : forall m' P, ainvF m' P -> munch WaF m m'.
  Proof. intros m' P (_ & _ & _ & _ & _ & _ & MU & _). exact MU. Qed.

  Lemma ainvF_ok : forall m' P k, ainvF m' P -> k = Z.of_nat (length P) -> (length P < 20)%nat ->
    store_ok rsegs m' (wa (bv_unsigned wo + k)) 1 = true.
  Proof. intros m' P k (_ & WO & _) Hk Hl. apply (wr_at_store_ok rsegs m' (bv_unsigned wo) 32); [exact WO | lia | lia]. Qed.

  Lemma ainvF_ok0 : forall m', ainvF m' [] -> store_ok rsegs m' wo 1 = true.
  Proof.
    intros m' D0. pose proof (ainvF_ok m' [] 0 D0 eq_refl ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. rewrite (wa_of_var wo (bv_unsigned wo) eq_refl) in H. exact H.
  Qed.

  Lemma ainvF_store : forall m' P (A v : word), ainvF m' P -> (length P < 20)%nat ->
    A = wa (bv_unsigned wo + Z.of_nat (length P)) ->
    ainvF (write_to_mem m' A (le1 v)) (P ++ [Z_to_bv 8 (bv_unsigned v)]).
  Proof.
    intros m' P A v ((jk & FR) & WO & BP & B20 & B5 & BD & MU & WM & MI & ST) Hl ->.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (Z.of_nat (length P)) 1 WO ltac:(lia) ltac:(lia)) as HS.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split.
    { apply (bytes_at_cat _ _ _ (bv_unsigned wo + Z.of_nat (length P))); [| | reflexivity].
      - apply bytes_at_write_other; [exact BP | lia | cbn [length]; lia | left; lia].
      - apply bytes_at_write_same; cbn [length]; lia. }
    split; [apply bytes_at_write_other; [exact B20 | lia | cbn [length]; lia | rewrite LJ20; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact B5 | lia | cbn [length]; lia | rewrite LP5; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact BD | lia | cbn [length]; lia | rewrite HLD; cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside WaF length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply stk_write; [exact ST | lia | cbn [length]; lia].
  Qed.

  (* The proof of munch WaF m mc for the current memory mc. *)
  Ltac bmuF mc :=
    lazymatch goal with
    | PI : ainvF mc _ |- _ => constr:(ainvF_mu mc _ PI)
    | MU : munch _ _ mc |- _ => constr:(MU)
    end.

  Ltac bjoinF G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

  Ltac steps_toF P :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; steps_toF P
    end.

  (* The check at pc P (srli, add s3, lb, bnez; slow path andi, blt) of address X = o + j; the shadow byte read by
     the lb is the one byte RSo1 gives for X. *)
  Ltac chkF P X j r :=
    steps_toF P;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      let MU := bmuF mc in
      let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
      let RS1 := fresh "RS1" in
      destruct (bdaF_shadow mc X j MU ltac:(lia) ltac:(lia)) as (k & RK & OK & KR);
      step;
      rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
      assert (RS1 : rng RNG (X / 8 + off) 1) by (apply RSo1; lia);
      step; step; clear RK; step;
      unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
      lazymatch goal with
      | |- evtF ?segs ?rg ?Q (MS ?R ?FF (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evtF segs rg Q (MS (bvmap_set r rr R) FF B fc rv mm ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ bjoinF G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              bjoinF G r ]
          | intros ?; simp_regs; clear OK KR RS1 ]
      end
    end.

  Ltac to_storeF mc :=
    step;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc _ _) _) => idtac
    | _ => to_storeF mc
    end.

  (* The store of header byte k. *)
  Ltac astF k :=
    lazymatch goal with
    | PI : ainvF ?mc ?P |- _ =>
        let HS := fresh "HS" in
        first [ pose proof (ainvF_ok0 mc PI) as HS
              | pose proof (ainvF_ok mc P k PI eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
        to_storeF mc;
        clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
            let PI' := fresh "PI" in
            pose proof (ainvF_store mc P A v PI ltac:(apply Nat.ltb_lt; reflexivity)
                          ltac:(first [reflexivity | apply rc_wa_add0])) as PI';
            clear PI;
            let mc' := fresh "mc" in
            set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
        end
    end.

  (* +0x338 .. +0x350: the epilogue. *)
  Lemma epiaF : forall x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    fraF m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86dcc) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) HB MU WM MI ST.
    destruct (bdaF_rt m' MU WM) as [AC SR].
    pose proof (stk_release rsegs m' _ _ _ ST FR ltac:(lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in ST' by lia.
    step. step. step. step. step. step. step.
    apply evtF_done. unfold QaF. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST'|]. split; [exact AC | exact SR].
  Qed.

  (* +0x31c .. +0x334: the check and store of the block check byte at o + 31. *)
  Lemma finaF : forall u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86db0) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO HB MU WM MI ST.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) 31) as PR. change (Z.of_nat 31) with 31 in PR.
    chkF 0x86db4 (bv_unsigned wo + 31) 31 (Z_to_bv 5 13).
    step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
    step.
    first [ rewrite (bda_neg (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) by lia
          | rewrite (bda_neg' (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) ].
    destruct (ostF m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                ltac:(cbn [inside WaF]; right; right; left; split; lia) FR WO MU WM MI ST)
      as (FR' & WO' & MU' & WM' & MI' & ST' & B31).
    eapply epiaF; [exact FR' | | exact MU' | exact WM' | exact MI' | exact ST'].
    unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
    apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
  Qed.

  (* +0x2e4 .. +0x318: the block sum loop over o .. o + 30, each load checked. *)
  Lemma outeraF : forall k i u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    x10 = Z_to_bv 64 (bv_unsigned wo + Z.of_nat i) ->
    x13 = Z_to_bv 64 (bv_unsigned wo + Z.of_nat i) ->
    bv_unsigned x12 = Z.of_nat k ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86d78) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk E10 E13 H12 FR WO HB MU WM MI ST;
      [lia|].
    subst x10 x13.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    chkF 0x86d78 (bv_unsigned wo + Z.of_nat i) (Z.of_nat i) (Z_to_bv 5 15).
    step. step. step. step.
    rewrite psum_S_zxb.
    step. step.
    rewrite (rc_eqb0 (bv_unsigned x12 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x12 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      replace (S i) with 31%nat by lia.
      eapply finaF; eassumption.
    - replace (bv_unsigned x12 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia | rewrite unsigned_lit by lia; lia].
  Qed.

  (* +0x294 .. +0x2e0: the record check byte at o + 20 + n, the byte 247 at o + 21 + n, each store checked. *)
  Lemma tailaF : forall u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4))) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86d28) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO Bhd B5 MU WM MI ST.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) as PR.
    chkF 0x86d30 (bv_unsigned wo + bv_unsigned wn + 20) (bv_unsigned wn + 20) (Z_to_bv 5 13).
    step. step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
    step.
    rewrite rc_le1_stamp.
    change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
    destruct (ostF m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                ltac:(cbn [inside WaF]; right; left; split; lia) FR WO MU WM MI ST)
      as (FR1 & WO1 & MU1 & WM1 & MI1 & ST1 & Bick).
    pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ Bhd ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LHD; cbn [length]; lia)) as Bhd1.
    pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ B5 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LP5; cbn [length]; lia)) as B51.
    unfold wa in *.
    remember (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 20)))
                [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)]) as m1 eqn:Em1.
    clear Em1.
    chkF 0x86d50 (bv_unsigned wo + bv_unsigned wn + 21) (bv_unsigned wn + 21) (Z_to_bv 5 12).
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
    step. step. step.
    rewrite rc_le1_lit.
    replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
    destruct (ostF m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                ltac:(cbn [inside WaF]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1 ST1)
      as (FR2 & WO2 & MU2 & WM2 & MI2 & ST2 & Bf7).
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ Bhd1 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LHD; cbn [length]; lia)) as Bhd2.
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ B51 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LP5; cbn [length]; lia)) as B52.
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ Bick ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(cbn [length]; lia)) as Bick2.
    unfold wa in *.
    remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 21))) [Z_to_bv 8 247])
      as m2 eqn:Em2.
    clear Em2.
    step. step. step.
    eapply outeraF with (k := 31%nat) (i := 0%nat);
      [lia | lia | | | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2 | exact ST2].
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self.
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self.
    - rewrite unsigned_lit by lia. reflexivity.
    - unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
      change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
        with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
  Qed.

  (* +0x25c .. +0x290: the record sum loop over o + 16 .. o + 19 + n, each load checked. *)
  Lemma inneraF : forall k i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    x10 = Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i) ->
    x18 = Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i) ->
    bv_unsigned x12 = Z.of_nat k ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86cf0) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk E10 E18 H12 FR WO Bhd B5 MU WM MI ST;
      [lia|].
    subst x10 x18.
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    chkF 0x86cf0 (bv_unsigned wo + 16 + Z.of_nat i) (16 + Z.of_nat i) (Z_to_bv 5 14).
    step. step. step. step.
    rewrite psum_S_zxb.
    step. step.
    rewrite (rc_eqb0 (bv_unsigned x12 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x12 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      replace (S i) with (nn + 4)%nat by lia.
      eapply tailaF; eassumption.
    - replace (bv_unsigned x12 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia | rewrite unsigned_lit by lia; lia].
  Qed.

  (* +0x238 .. +0x258: the call __asan_memcpy(o + 20, d, n), then the record sum loop. *)
  Lemma callpF : forall u0 u1 u2 x10 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    ainvF m' (dt1_hdr nn (bv_unsigned wv)) ->
    evtF rsegs RNG QaF
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn x10 wv wd x13 x14 x15 x16 x17
               (Z_to_bv 64 (bv_unsigned wo + 16)) (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86ccc) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' PI.
    destruct PI as ((jk & FR) & WO & BH & B20 & B5 & BD & MU & WM & MI & ST).
    pose proof (dt1_hdr_length nn (bv_unsigned wv)) as LH.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdaF_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable WaF m m' _ _ HADd MU bdaF_so) as AD'.
    pose proof (fl_addressable WaF m m' _ _ HADo MU bdaF_so) as AO'.
    (* the shared statement, with its shadow word spans (sh_word_rng of asan_memcpy_cF.v) written out *)
    pose proof HMC as HM. unfold asan_memcpy_contract_F, sh_word_rng, sh_al8_lo, sh_al8_hi in HM. cbv zeta in HM.
    step. step. step. step.
    eapply evtF_cut.
    { eapply HM with (src := D) (junk := J20) (lo := bv_unsigned sp + -2272).
      all: rewrite ?(unsigned_lit (bv_unsigned wo + 20)) by lia;
           rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
           try unfold ASAN_MEMCPY_K.
      - exact BD.
      - lia.
      - split; [split|].
        + cbn [cells_wf cell_wf]. split; [lia | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B20.
        + cbn [cells_size csize]. rewrite Nat.add_0_r.
          replace (Z.of_nat (Z.to_nat (bv_unsigned wn))) with (bv_unsigned wn) by lia.
          apply (wr_at_sub _ _ _ 32 20 (bv_unsigned wn) WO); lia.
      - lia.
      - lia.
      - exact AD'.
      - apply (bda_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - exact HEd.
      - right. replace (bv_unsigned wo + 20 + bv_unsigned wn) with (bv_unsigned wo + (20 + bv_unsigned wn)) by lia.
        apply bdaF_app_o. lia.
      - destruct H7d as [H0 | H7]; [left; exact H0 | right; split; [exact H7|]].
        replace (bv_unsigned wo + 20 + 7) with (bv_unsigned wo + 27) by lia. apply bdaF_app_o. lia.
      - lia.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - lia.
      - lia.
      - exact AC.
      - exact SR.
      - exact MI.
      - exact RBY.
      (* the regions of the call: the image, its window below sp - 48, the n bytes written at o + 20, the n bytes
         read at d, the 8-aligned shadow word cover of each of those two, and the 8-aligned shadow word span of its
         window *)
      - exact RIMG.
      - eapply rng_sub; [exact RWIN | lia | lia].
      - eapply rng_sub; [exact ROUT | lia | lia].
      - eapply rng_sub; [exact RDAT | lia | lia].
      - destruct (Z.eq_dec (bv_unsigned wn) 0) as [E0|E0]; [left; exact E0 | right].
        unfold shadow_addr.
        exact (RSoK (bv_unsigned wo + 20) (bv_unsigned wo + 20 + bv_unsigned wn - 1)
                 ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (bv_unsigned wn) 0) as [E0|E0]; [left; exact E0 | right].
        unfold shadow_addr.
        exact (RSdK (bv_unsigned wd) (bv_unsigned wd + bv_unsigned wn - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - right. unfold shadow_addr.
        exact (RWSK (bv_unsigned sp + -48 - 2224) (bv_unsigned sp + -48 - 2224 + 2224 - 1)
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3' & a4'' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m3
                    & E & MU3 & WM3 & MI3 & ST3 & RW3 & BD3 & AC3 & SR3).
    subst ms'. clear BD3 AC3 SR3.
    rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in MU3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in RW3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in MU3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia.
    unfold ASAN_MEMCPY_K in MU3.
    assert (SUBc : sub_fp [(bv_unsigned wo + 20, bv_unsigned wo + 20 + bv_unsigned wn);
                           (bv_unsigned sp + -48 - 2224, bv_unsigned sp + -48)] WaF).
    { intros x Hx. unfold WaF in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
      split; [lia|]. split; [lia | exact I]. }
    pose proof (munch_trans WaF m m' m3 MU (munch_weaken _ WaF m' m3 SUBc MU3)) as MU4.
    pose proof (wmono_trans rsegs m m' m3 WM WM3) as WM4.
    pose proof (rw_cells_transport rsegs _ m' m3 _ _ FR MU3 WM3) as FR4.
    specialize (FR4 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (wr_at_transport rsegs m' m3 _ _ WO WM3) as WO4.
    pose proof (bytes_at_transport rsegs _ m' m3 _ _ BH MU3) as BH4.
    specialize (BH4 ltac:(rewrite LH; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m3 _ _ B5 MU3) as B54.
    specialize (B54 ltac:(rewrite LP5; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    destruct RW3 as [[_ BD3] _]. cbn [cells_bytes cbytes] in BD3. rewrite app_nil_r in BD3.
    clear FR WO BH B5 BD B20 MU WM MI ST MU3 WM3 AD' AO' AC SR.
    replace (ret_pc (Z_to_bv 64 0x86cdc)) with (Z_to_bv 64 0x86cdc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step. step. step. step.
    eapply inneraF with (k := (nn + 4)%nat) (i := 0%nat);
      [lia | lia | | | | eexists; exact FR4 | exact WO4 | | exact B54 | exact MU4 | exact WM4 | exact MI3 | exact ST3].
    - f_equal. lia.
    - f_equal. lia.
    - rewrite ?(unsigned_lit (bv_unsigned wn + 4)) by lia. rewrite bda_zext by lia. lia.
    - apply (bytes_at_cat _ _ _ (bv_unsigned wo + 20)); [exact BH4 | exact BD3 | rewrite LH; lia].
  Qed.

  (* +0x2c .. +0x234: the 20 header stores, each checked. *)
  Lemma midF : forall u0 u1 u2 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    ainvF m' [] ->
    evtF rsegs RNG QaF
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn wo wv wd x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86ac0) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' PI.
    pose proof (zr_word wv) as Rv. unfold inr64 in Rv.
    chkF 0x86ac0 (bv_unsigned wo) 0 (Z_to_bv 5 13). astF 0.
    chkF 0x86adc (bv_unsigned wo + 1) 1 (Z_to_bv 5 14). astF 1.
    chkF 0x86af8 (bv_unsigned wo + 2) 2 (Z_to_bv 5 14). astF 2.
    chkF 0x86b10 (bv_unsigned wo + 3) 3 (Z_to_bv 5 14). astF 3.
    chkF 0x86b2c (bv_unsigned wo + 4) 4 (Z_to_bv 5 14). astF 4.
    chkF 0x86b44 (bv_unsigned wo + 5) 5 (Z_to_bv 5 14). astF 5.
    chkF 0x86b60 (bv_unsigned wo + 6) 6 (Z_to_bv 5 14). astF 6.
    chkF 0x86b78 (bv_unsigned wo + 7) 7 (Z_to_bv 5 14). astF 7.
    chkF 0x86b94 (bv_unsigned wo + 8) 8 (Z_to_bv 5 14). astF 8.
    chkF 0x86bb0 (bv_unsigned wo + 9) 9 (Z_to_bv 5 14). astF 9.
    chkF 0x86bcc (bv_unsigned wo + 10) 10 (Z_to_bv 5 14). astF 10.
    chkF 0x86be8 (bv_unsigned wo + 11) 11 (Z_to_bv 5 14). astF 11.
    chkF 0x86c04 (bv_unsigned wo + 12) 12 (Z_to_bv 5 14). astF 12.
    chkF 0x86c1c (bv_unsigned wo + 13) 13 (Z_to_bv 5 14). astF 13.
    chkF 0x86c34 (bv_unsigned wo + 14) 14 (Z_to_bv 5 14). astF 14.
    chkF 0x86c50 (bv_unsigned wo + 15) 15 (Z_to_bv 5 15). astF 15.
    chkF 0x86c68 (bv_unsigned wo + 16) 16 (Z_to_bv 5 13). astF 16.
    chkF 0x86c84 (bv_unsigned wo + 17) 17 (Z_to_bv 5 14). astF 17.
    chkF 0x86c9c (bv_unsigned wo + 18) 18 (Z_to_bv 5 14). astF 18.
    chkF 0x86cb8 (bv_unsigned wo + 19) 19 (Z_to_bv 5 14). astF 19.
    match goal with H : ainvF _ ?P |- _ =>
      assert (EH : P = dt1_hdr nn (bv_unsigned wv)); [|rewrite EH in H]
    end.
    { cbn [app]. unfold dt1_hdr, dt1_bytes. cbn [map].
      repeat apply rc_cons_eq;
        first [ reflexivity
              | apply Z_to_bv8_mod; rewrite unsigned_lit_wrap; rewrite mod_mod8_of_modw by lia;
                first [reflexivity | f_equal; lia] ]. }
    clear EH.
    eapply callpF; eassumption.
  Qed.
End BDAF.

Theorem build_dt1_single_F_holds : asan_memcpy_contract_F -> build_dt1_single_contract_F.
Proof.
  intros HMC. unfold build_dt1_single_contract_F, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo
    RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ro. unfold inr64 in Ro.
  pose proof (zr_word a2) as Rd. unfold inr64 in Rd.
  pose proof (zr_word a3) as Rn. unfold inr64 in Rn.
  assert (Hsp : 2272 <= bv_unsigned sp) by (unfold HIGHMEM_BEG in HHM; lia).
  pose proof (bda_shadow_out m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HADo ltac:(lia)) as SO.
  pose proof (bda_rt_out (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HRTo ltac:(lia)) as RO.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 32 _ HADo SO) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 32 HADo) as HAD.
  pose proof (rt_asan_rt m _ HCE
                (fun x Hx => match Hx with
                             | or_introl H => RO x ltac:(unfold GOT_CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_introl H) => RO x ltac:(unfold CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_intror H) => SO x H
                             end)) as HRT.
  (* the two runtime cells are read at literal addresses: keep unfolded copies of their rng premises *)
  assert (RGz : rng RNG GOT_CELL_K 8)
    by (eapply rng_sub; [exact RRT | unfold GOT_CELL_K, RT_LO, RT_HI; lia | unfold GOT_CELL_K, RT_LO, RT_HI; lia]).
  assert (RCz : rng RNG CELL_K 8)
    by (eapply rng_sub; [exact RRT | unfold CELL_K, RT_LO, RT_HI; lia | unfold CELL_K, RT_LO, RT_HI; lia]).
  unfold GOT_CELL_K in RGz. unfold CELL_K in RCz.
  (* the three consequences of the two aligned shadow covers that the run uses *)
  assert (RSo1 : forall x, bv_unsigned a0 <= x <= bv_unsigned a0 + 31 -> rng RNG (x / 8 + ASAN_K) 1)
    by (intros x Hx; exact (bdaF_sh1 RNG ASAN_K _ _ x RSO Hx)).
  assert (RSoK : forall u v, bv_unsigned a0 <= u -> u <= v -> v <= bv_unsigned a0 + 31 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8))
    by (intros u v H1 H2 H3; exact (bdaF_shK RNG ASAN_K _ _ u v RSO H1 H2 H3)).
  assert (RSdK : forall u v, bv_unsigned a2 <= u -> u <= v -> v <= bv_unsigned a2 + bv_unsigned a3 - 1 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8)).
  { intros u v H1 H2 H3. destruct RSD as [E0 | RSD'];
      [exfalso; lia | exact (bdaF_shK RNG ASAN_K _ _ u v RSD' H1 H2 H3)]. }
  assert (RWSK : forall u v, bv_unsigned sp - 2272 <= u -> u <= v -> v <= bv_unsigned sp - 1 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8))
    by (intros u v H1 H2 H3;
        exact (bdaF_wincov RNG (bv_unsigned sp - 2272) 2272 u v RWS ltac:(lia) H1 H2 ltac:(lia))).
  clear RWS.
  set (off := ASAN_K) in HSR, HAD, HRT, RSo1. clearbody off.
  destruct HO as [[Hwf HOB] WO]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lob _].
  cbn [cells_bytes cbytes cells_size csize Nat.add] in HOB, WO. rewrite app_nil_r in HOB.
  change (Z.of_nat 32) with 32 in WO.
  remember (Z.to_nat (bv_unsigned a3)) as nn eqn:Enn.
  assert (Hnn : Z.of_nat nn = bv_unsigned a3) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step. step.
  clear RG RC HRT HRT1.
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply midF; try eassumption; try lia.
  split; [eexists; eassumption|]. split; [assumption|]. split; [apply bytes_at_nil; lia|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
Qed.

(* RECIPE step 1: the old theorem's statement, back from the footprint form at ExecF.RNG_all. The callee's
   footprint form stands in the place where build_dt1_single_holds takes asan_memcpy_contract. *)
Theorem build_dt1_single_holds_of_F : asan_memcpy_contract_F -> build_dt1_single_contract.
Proof. intros HMC. exact (build_dt1_single_contract_of_F (build_dt1_single_F_holds HMC)). Qed.

(* With no hypothesis left: the footprint statement of this function at the callee contract its owner proves for
   this image -- a Theorem Labs lane's asan_memcpy_holds_F (lib/A/Prog/asan_memcpyF.v). *)
Corollary build_dt1_single_F_holds_closed : build_dt1_single_contract_F.
Proof.
  exact (build_dt1_single_F_holds
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF.asan_memcpy_holds_F).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane): build_dt1_single_F_holds_on proves the _F_on twin
   build_dt1_single_contract_F_on (a Theorem Labs lane's build_dt1_single_c.v, taken by path) from the footprint _on contract of
   __asan_memcpy, a Theorem Labs lane's asan_memcpy_contract_F_on (asan_memcpy_cF_on.v). It is the port into this footprint walk
   of a Theorem Labs lane's Module BDAon (build_dt1_single.v, a working branch ec2ad5b4f4f): Module BDAFon holds
   Section BDAF again with the same changes BDAon makes to Section BDA. HMC is the footprint _on contract of
   __asan_memcpy; HSW is the region premise shadow_rw_on R m with R = build_dt1_single_shadow_R o d n, the region of
   __asan_memcpy at its one call (o + 20, d, n); the shadow conjunct of QaF (given by bdaF_rt) is the region transport
   (each region the caller holds in m it holds in m'), by ShadowRwOnK.fl_shadow_rw_on with bdaF_so; at the call
   (callpF) the callee's region is R, carried from m to the memory of the call by bdaF_rt. The run stores no shadow
   byte, and its own checks of the 32 bytes at o read their shadow through `addressable m o 32` (rt_shadow_rd), not
   through HSW. build_dt1_single_F_holds above keeps its premise, the footprint form of the OLD contract of
   __asan_memcpy, which does not give the _on contract; it stays as it is. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpy_c_on asan_memcpy_cF_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF_on.

Module BDAFon.
Section BDAF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 J20 : list byte) (nn : nat) (off : Z)
    (RNG : footprint).
  Hypothesis HMC : A.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on.
  Hypothesis Rsp : 0 <= bv_unsigned sp < 2^64.
  Hypothesis Hsp : 2272 <= bv_unsigned sp.
  Hypothesis Ro : 0 <= bv_unsigned wo.
  Hypothesis Ho32 : bv_unsigned wo + 32 <= 2^64.
  Hypothesis Rd : 0 <= bv_unsigned wd.
  Hypothesis Hd : bv_unsigned wd + bv_unsigned wn <= 2^64.
  Hypothesis Hnn : Z.of_nat nn = bv_unsigned wn.
  Hypothesis Hn9 : (nn <= 9)%nat.
  Hypothesis HLD : length D = nn.
  Hypothesis Lob : length ob = 32%nat.
  Hypothesis LJ20 : length J20 = nn.
  Hypothesis EP5 : P5 = firstn (9 - nn) (skipn (22 + nn) ob).
  Hypothesis DfO : bv_unsigned sp <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned sp - 2272.
  Hypothesis DdO : bv_unsigned wd + bv_unsigned wn <= bv_unsigned wo \/ bv_unsigned wo + 32 <= bv_unsigned wd.
  Hypothesis Dfd : bv_unsigned sp <= bv_unsigned wd \/ bv_unsigned wd + bv_unsigned wn <= bv_unsigned sp - 2272.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 2272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis HCE : asan_cells m.
  Hypothesis HSW :
    A.ShadowRwOn.shadow_rw_on (build_dt1_single_shadow_R (bv_unsigned wo) (bv_unsigned wd) (bv_unsigned wn)) m.
  Hypothesis HADo : addressable m (bv_unsigned wo) 32.
  Hypothesis HADd : addressable m (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis HAPo : app_mem (bv_unsigned wo + 32).
  Hypothesis HEd : end_in_app (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis H7d : bv_unsigned wn = 0 \/ app_mem (bv_unsigned wd + 7).
  Hypothesis HRTo : bv_unsigned wo + 32 <= RT_LO \/ RT_HI <= bv_unsigned wo.

  (* The contract's footprint. *)
  Definition WaF : list ivl :=
    [(bv_unsigned sp + -2272, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  (* The shadow bytes of the 32 bytes at o, read in m, with the offset off that s3 holds. *)
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned wo) 32 WaF.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned wo) 32.

  (* The rng premises of build_dt1_single_contract_F: the image [IMG_LO, IMG_HI), which the callee's _F contract
     takes; the window K below sp (this 48-byte frame and the window of __asan_memcpy below it) and the 8-aligned
     shadow word span of that window, which holds the shadow of the callee's frame; the runtime words, which hold
     the GOT cell and the cell of the shadow offset; the 32 bytes at o and the n bytes at d; and the shadow bytes of
     those two ranges.
     The shadow premises are QUANTIFIED, and that is deliberate: `lia` unfolds `rng` (it is a transparent
     conjunction of bounds), so a ground premise whose bounds hold nested `/ 8` terms puts Euclidean variables into
     every `lia` call of the script below. Under a `forall`, zify skips the premise, and the run draws exactly the
     consequences it needs: one shadow byte per checked byte (RSo1, with the offset off that the run reads out of
     the runtime cell), and the 8-aligned shadow word cover of a sub-range (RSoK / RSdK / RWSK, with ASAN_K, the
     shape the callee's _F contract names). The caller discharges them from the aligned-cover premises of
     build_dt1_single_contract_F, where off is ASAN_K. *)
  (* The footprint is decided byte by byte: the callee's _F contract takes this. *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG IMG_LO (IMG_HI - IMG_LO).
  Hypothesis RWIN : rng RNG (bv_unsigned sp - 2272) 2272.
  Hypothesis RRT : rng RNG RT_LO (RT_HI - RT_LO).
  Hypothesis ROUT : rng RNG (bv_unsigned wo) 32.
  Hypothesis RDAT : rng RNG (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis RSo1 : forall x, bv_unsigned wo <= x <= bv_unsigned wo + 31 -> rng RNG (x / 8 + off) 1.
  Hypothesis RSoK : forall a b, bv_unsigned wo <= a -> a <= b -> b <= bv_unsigned wo + 31 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis RSdK : forall a b, bv_unsigned wd <= a -> a <= b -> b <= bv_unsigned wd + bv_unsigned wn - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
  Hypothesis RWSK : forall a b, bv_unsigned sp - 2272 <= a -> a <= b -> b <= bv_unsigned sp - 1 ->
    rng RNG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

  Definition QaF : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch WaF m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp)
      /\ asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m').

  Definition fraF (m' : word -> option byte) : Prop :=
    exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma bdaF_so : forall x, in_shadow x -> outside WaF x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bda_shadow_out m (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HADo ltac:(lia)).
  Qed.

  Lemma bdaF_ro : forall x, RT_LO <= x < RT_HI -> outside WaF x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bda_rt_out (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HRTo ltac:(lia)).
  Qed.

  (* The runtime's cells and the shadow are outside WaF: a run that writes only WaF keeps the cells and each shadow
     region present in m. *)
  Lemma bdaF_rt : forall m', munch WaF m m' -> wmono rsegs m m' ->
    asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m').
  Proof.
    intros m' MU WM. split.
    - exact (fl_asan_cells WaF m m' HCE MU bdaF_ro).
    - intros P HP. exact (A.ShadowRwOnK.fl_shadow_rw_on P WaF m m' HP MU WM bdaF_so).
  Qed.

  Lemma bdaF_app_o : forall t, 0 <= t <= 32 -> app_mem (bv_unsigned wo + t).
  Proof.
    intros t Ht. apply bda_app_mid; [|exact HAPo|exact Ht].
    pose proof (bda_addr_app m _ 32 0 HADo ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
  Qed.

  (* The check of byte o + j in a memory m' that the run reached writing only WaF. *)
  Lemma bdaF_shadow : forall m' X j, munch WaF m m' -> 0 <= j < 32 -> X = bv_unsigned wo + j ->
    exists k : byte, ov_read_bytes rsegs m' (wa (X / 8 + off)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros m' X j MU Hj ->.
    pose proof (asan_shadow_rd_munch rsegs m m' off _ 32 WaF WaF HSR MU (fun x Hx => Hx)) as HR'.
    pose proof (asan_addressable_munch rsegs m m' off _ 32 WaF WaF HAD HSR MU (fun x Hx => Hx)) as HA'.
    destruct (asan_shadow_read rsegs m' off _ 32 WaF j HR' Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HA' j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A store of one byte at o + j, 0 <= j < 32, inside WaF. *)
  Lemma ostF : forall m' j (b : byte), 0 <= j < 32 -> inside WaF (bv_unsigned wo + j) 1 ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    fraF (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch WaF m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wmono rsegs m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    mem_inv rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    stk rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned sp + -2272) (bv_unsigned sp + -48) /\
    bytes_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo + j) [b].
  Proof.
    intros m' j b Hj Hin (jk & FR) WO MU WM MI ST.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 j 1 WO ltac:(lia) ltac:(lia)) as HS.
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | exact Hin]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    split; [apply stk_write; [exact ST | lia | cbn [length]; lia]|].
    apply bytes_at_write_same; cbn [length]; lia.
  Qed.

  (* The state of the header stores: P is the part of the header written so far. *)
  Definition ainvF (m' : word -> option byte) (P : list byte) : Prop :=
    fraF m' /\ wr_at rsegs m' (bv_unsigned wo) 32 /\ bytes_at rsegs m' (bv_unsigned wo) P /\
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 /\ bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 /\
    bytes_at rsegs m' (bv_unsigned wd) D /\
    munch WaF m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48).

  Lemma ainvF_mu : forall m' P, ainvF m' P -> munch WaF m m'.
  Proof. intros m' P (_ & _ & _ & _ & _ & _ & MU & _). exact MU. Qed.

  Lemma ainvF_ok : forall m' P k, ainvF m' P -> k = Z.of_nat (length P) -> (length P < 20)%nat ->
    store_ok rsegs m' (wa (bv_unsigned wo + k)) 1 = true.
  Proof. intros m' P k (_ & WO & _) Hk Hl. apply (wr_at_store_ok rsegs m' (bv_unsigned wo) 32); [exact WO | lia | lia]. Qed.

  Lemma ainvF_ok0 : forall m', ainvF m' [] -> store_ok rsegs m' wo 1 = true.
  Proof.
    intros m' D0. pose proof (ainvF_ok m' [] 0 D0 eq_refl ltac:(cbn; lia)) as H.
    rewrite Z.add_0_r in H. rewrite (wa_of_var wo (bv_unsigned wo) eq_refl) in H. exact H.
  Qed.

  Lemma ainvF_store : forall m' P (A v : word), ainvF m' P -> (length P < 20)%nat ->
    A = wa (bv_unsigned wo + Z.of_nat (length P)) ->
    ainvF (write_to_mem m' A (le1 v)) (P ++ [Z_to_bv 8 (bv_unsigned v)]).
  Proof.
    intros m' P A v ((jk & FR) & WO & BP & B20 & B5 & BD & MU & WM & MI & ST) Hl ->.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (Z.of_nat (length P)) 1 WO ltac:(lia) ltac:(lia)) as HS.
    change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
    split; [exists jk; apply rw_cells_frame; [exact FR | lia | cbn [length]; lia | cbn [cells_size csize Nat.add length]; lia]|].
    split; [apply wr_at_write; exact WO|].
    split.
    { apply (bytes_at_cat _ _ _ (bv_unsigned wo + Z.of_nat (length P))); [| | reflexivity].
      - apply bytes_at_write_other; [exact BP | lia | cbn [length]; lia | left; lia].
      - apply bytes_at_write_same; cbn [length]; lia. }
    split; [apply bytes_at_write_other; [exact B20 | lia | cbn [length]; lia | rewrite LJ20; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact B5 | lia | cbn [length]; lia | rewrite LP5; cbn [length]; lia]|].
    split; [apply bytes_at_write_other; [exact BD | lia | cbn [length]; lia | rewrite HLD; cbn [length]; lia]|].
    split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside WaF length]; right; left; split; lia]|].
    split; [apply wmono_write; exact WM|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    apply stk_write; [exact ST | lia | cbn [length]; lia].
  Qed.

  (* The proof of munch WaF m mc for the current memory mc. *)
  Ltac bmuF mc :=
    lazymatch goal with
    | PI : ainvF mc _ |- _ => constr:(ainvF_mu mc _ PI)
    | MU : munch _ _ mc |- _ => constr:(MU)
    end.

  Ltac bjoinF G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

  Ltac steps_toF P :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; steps_toF P
    end.

  (* The check at pc P (srli, add s3, lb, bnez; slow path andi, blt) of address X = o + j; the shadow byte read by
     the lb is the one byte RSo1 gives for X. *)
  Ltac chkF P X j r :=
    steps_toF P;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      let MU := bmuF mc in
      let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
      let RS1 := fresh "RS1" in
      destruct (bdaF_shadow mc X j MU ltac:(lia) ltac:(lia)) as (k & RK & OK & KR);
      step;
      rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
      assert (RS1 : rng RNG (X / 8 + off) 1) by (apply RSo1; lia);
      step; step; clear RK; step;
      unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
      lazymatch goal with
      | |- evtF ?segs ?rg ?Q (MS ?R ?FF (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evtF segs rg Q (MS (bvmap_set r rr R) FF B fc rv mm ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ bjoinF G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              bjoinF G r ]
          | intros ?; simp_regs; clear OK KR RS1 ]
      end
    end.

  Ltac to_storeF mc :=
    step;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc _ _) _) => idtac
    | _ => to_storeF mc
    end.

  (* The store of header byte k. *)
  Ltac astF k :=
    lazymatch goal with
    | PI : ainvF ?mc ?P |- _ =>
        let HS := fresh "HS" in
        first [ pose proof (ainvF_ok0 mc PI) as HS
              | pose proof (ainvF_ok mc P k PI eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
        to_storeF mc;
        clear HS;
        lazymatch goal with
        | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
            let PI' := fresh "PI" in
            pose proof (ainvF_store mc P A v PI ltac:(apply Nat.ltb_lt; reflexivity)
                          ltac:(first [reflexivity | apply rc_wa_add0])) as PI';
            clear PI;
            let mc' := fresh "mc" in
            set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
        end
    end.

  (* +0x338 .. +0x350: the epilogue. *)
  Lemma epiaF : forall x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    fraF m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86dcc) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) HB MU WM MI ST.
    destruct (bdaF_rt m' MU WM) as [AC SR].
    pose proof (stk_release rsegs m' _ _ _ ST FR ltac:(lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in ST' by lia.
    step. step. step. step. step. step. step.
    apply evtF_done. unfold QaF. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST'|]. split; [exact AC | exact SR].
  Qed.

  (* +0x31c .. +0x334: the check and store of the block check byte at o + 31. *)
  Lemma finaF : forall u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86db0) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO HB MU WM MI ST.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) 31) as PR. change (Z.of_nat 31) with 31 in PR.
    chkF 0x86db4 (bv_unsigned wo + 31) 31 (Z_to_bv 5 13).
    step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
    step.
    first [ rewrite (bda_neg (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) by lia
          | rewrite (bda_neg' (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) ].
    destruct (ostF m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                ltac:(cbn [inside WaF]; right; right; left; split; lia) FR WO MU WM MI ST)
      as (FR' & WO' & MU' & WM' & MI' & ST' & B31).
    eapply epiaF; [exact FR' | | exact MU' | exact WM' | exact MI' | exact ST'].
    unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
    apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
  Qed.

  (* +0x2e4 .. +0x318: the block sum loop over o .. o + 30, each load checked. *)
  Lemma outeraF : forall k i u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    x10 = Z_to_bv 64 (bv_unsigned wo + Z.of_nat i) ->
    x13 = Z_to_bv 64 (bv_unsigned wo + Z.of_nat i) ->
    bv_unsigned x12 = Z.of_nat k ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86d78) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x9 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk E10 E13 H12 FR WO HB MU WM MI ST;
      [lia|].
    subst x10 x13.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    chkF 0x86d78 (bv_unsigned wo + Z.of_nat i) (Z.of_nat i) (Z_to_bv 5 15).
    step. step. step. step.
    rewrite psum_S_zxb.
    step. step.
    rewrite (rc_eqb0 (bv_unsigned x12 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x12 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      replace (S i) with 31%nat by lia.
      eapply finaF; eassumption.
    - replace (bv_unsigned x12 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia | rewrite unsigned_lit by lia; lia].
  Qed.

  (* +0x294 .. +0x2e0: the record check byte at o + 20 + n, the byte 247 at o + 21 + n, each store checked. *)
  Lemma tailaF : forall u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4))) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86d28) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO Bhd B5 MU WM MI ST.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) as PR.
    chkF 0x86d30 (bv_unsigned wo + bv_unsigned wn + 20) (bv_unsigned wn + 20) (Z_to_bv 5 13).
    step. step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
    step.
    rewrite rc_le1_stamp.
    change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
    destruct (ostF m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                ltac:(cbn [inside WaF]; right; left; split; lia) FR WO MU WM MI ST)
      as (FR1 & WO1 & MU1 & WM1 & MI1 & ST1 & Bick).
    pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ Bhd ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LHD; cbn [length]; lia)) as Bhd1.
    pose proof (bytes_at_write_other rsegs m' (bv_unsigned wo + (bv_unsigned wn + 20))
                  [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] _ _ B5 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LP5; cbn [length]; lia)) as B51.
    unfold wa in *.
    remember (write_to_mem m' (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 20)))
                [Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)]) as m1 eqn:Em1.
    clear Em1.
    chkF 0x86d50 (bv_unsigned wo + bv_unsigned wn + 21) (bv_unsigned wn + 21) (Z_to_bv 5 12).
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
    step. step. step.
    rewrite rc_le1_lit.
    replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
    destruct (ostF m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                ltac:(cbn [inside WaF]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1 ST1)
      as (FR2 & WO2 & MU2 & WM2 & MI2 & ST2 & Bf7).
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ Bhd1 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LHD; cbn [length]; lia)) as Bhd2.
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ B51 ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(rewrite LP5; cbn [length]; lia)) as B52.
    pose proof (bytes_at_write_other rsegs m1 (bv_unsigned wo + (bv_unsigned wn + 21))
                  [Z_to_bv 8 247] _ _ Bick ltac:(lia) ltac:(cbn [length]; lia)
                  ltac:(cbn [length]; lia)) as Bick2.
    unfold wa in *.
    remember (write_to_mem m1 (Z_to_bv 64 (bv_unsigned wo + (bv_unsigned wn + 21))) [Z_to_bv 8 247])
      as m2 eqn:Em2.
    clear Em2.
    step. step. step.
    eapply outeraF with (k := 31%nat) (i := 0%nat);
      [lia | lia | | | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2 | exact ST2].
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self.
    - rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self.
    - rewrite unsigned_lit by lia. reflexivity.
    - unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
      change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
        with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
  Qed.

  (* +0x25c .. +0x290: the record sum loop over o + 16 .. o + 19 + n, each load checked. *)
  Lemma inneraF : forall k i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    x10 = Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i) ->
    x18 = Z_to_bv 64 (bv_unsigned wo + 16 + Z.of_nat i) ->
    bv_unsigned x12 = Z.of_nat k ->
    fraF m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch WaF m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evtF rsegs RNG QaF
      (MS (mkR (Z_to_bv 64 0x86cdc) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i)) x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86cf0) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x10 x12 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk E10 E18 H12 FR WO Bhd B5 MU WM MI ST;
      [lia|].
    subst x10 x18.
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    chkF 0x86cf0 (bv_unsigned wo + 16 + Z.of_nat i) (16 + Z.of_nat i) (Z_to_bv 5 14).
    step. step. step. step.
    rewrite psum_S_zxb.
    step. step.
    rewrite (rc_eqb0 (bv_unsigned x12 + -1)) by lia.
    destruct k as [|k].
    - replace (bv_unsigned x12 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      step.
      replace (S i) with (nn + 4)%nat by lia.
      eapply tailaF; eassumption.
    - replace (bv_unsigned x12 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      apply (IH (S i)); first [lia | assumption | f_equal; lia | rewrite unsigned_lit by lia; lia].
  Qed.

  (* +0x238 .. +0x258: the call __asan_memcpy(o + 20, d, n), then the record sum loop. *)
  Lemma callpF : forall u0 u1 u2 x10 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    ainvF m' (dt1_hdr nn (bv_unsigned wv)) ->
    evtF rsegs RNG QaF
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn x10 wv wd x13 x14 x15 x16 x17
               (Z_to_bv 64 (bv_unsigned wo + 16)) (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86ccc) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' PI.
    destruct PI as ((jk & FR) & WO & BH & B20 & B5 & BD & MU & WM & MI & ST).
    pose proof (dt1_hdr_length nn (bv_unsigned wv)) as LH.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdaF_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable WaF m m' _ _ HADd MU bdaF_so) as AD'.
    pose proof (fl_addressable WaF m m' _ _ HADo MU bdaF_so) as AO'.
    (* the shared statement, with its shadow word spans (sh_word_rng of asan_memcpy_cF.v) written out *)
    pose proof HMC as HM.
    unfold A.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on, sh_word_rng, sh_al8_lo, sh_al8_hi in HM.
    cbv zeta in HM.
    step. step. step. step.
    eapply evtF_cut.
    { eapply HM with (src := D) (junk := J20) (lo := bv_unsigned sp + -2272).
      all: rewrite ?(unsigned_lit (bv_unsigned wo + 20)) by lia;
           rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
           try unfold ASAN_MEMCPY_K.
      - exact BD.
      - lia.
      - split; [split|].
        + cbn [cells_wf cell_wf]. split; [lia | exact I].
        + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B20.
        + cbn [cells_size csize]. rewrite Nat.add_0_r.
          replace (Z.of_nat (Z.to_nat (bv_unsigned wn))) with (bv_unsigned wn) by lia.
          apply (wr_at_sub _ _ _ 32 20 (bv_unsigned wn) WO); lia.
      - lia.
      - lia.
      - exact AD'.
      - apply (bda_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - exact HEd.
      - right. replace (bv_unsigned wo + 20 + bv_unsigned wn) with (bv_unsigned wo + (20 + bv_unsigned wn)) by lia.
        apply bdaF_app_o. lia.
      - destruct H7d as [H0 | H7]; [left; exact H0 | right; split; [exact H7|]].
        replace (bv_unsigned wo + 20 + 7) with (bv_unsigned wo + 27) by lia. apply bdaF_app_o. lia.
      - lia.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - lia.
      - lia.
      - exact AC.
      - (* the region of __asan_memcpy at (o + 20, d, n) is R, present in m' by bdaF_rt *)
        apply (A.ShadowRwOn.shadow_rw_on_mono
                 (build_dt1_single_shadow_R (bv_unsigned wo) (bv_unsigned wd) (bv_unsigned wn)));
          [|exact (SR _ HSW)].
        intros a Ha. unfold A.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Ha.
        rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in Ha by lia. exact Ha.
      - exact MI.
      - exact RBY.
      (* the regions of the call: the image, its window below sp - 48, the n bytes written at o + 20, the n bytes
         read at d, the 8-aligned shadow word cover of each of those two, and the 8-aligned shadow word span of its
         window *)
      - exact RIMG.
      - eapply rng_sub; [exact RWIN | lia | lia].
      - eapply rng_sub; [exact ROUT | lia | lia].
      - eapply rng_sub; [exact RDAT | lia | lia].
      - destruct (Z.eq_dec (bv_unsigned wn) 0) as [E0|E0]; [left; exact E0 | right].
        unfold shadow_addr.
        exact (RSoK (bv_unsigned wo + 20) (bv_unsigned wo + 20 + bv_unsigned wn - 1)
                 ltac:(lia) ltac:(lia) ltac:(lia)).
      - destruct (Z.eq_dec (bv_unsigned wn) 0) as [E0|E0]; [left; exact E0 | right].
        unfold shadow_addr.
        exact (RSdK (bv_unsigned wd) (bv_unsigned wd + bv_unsigned wn - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
      - right. unfold shadow_addr.
        exact (RWSK (bv_unsigned sp + -48 - 2224) (bv_unsigned sp + -48 - 2224 + 2224 - 1)
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3' & a4'' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m3
                    & E & MU3 & WM3 & MI3 & ST3 & RW3 & BD3 & AC3 & SR3).
    subst ms'. clear BD3 AC3 SR3.
    rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in MU3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in RW3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in MU3 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia.
    unfold ASAN_MEMCPY_K in MU3.
    assert (SUBc : sub_fp [(bv_unsigned wo + 20, bv_unsigned wo + 20 + bv_unsigned wn);
                           (bv_unsigned sp + -48 - 2224, bv_unsigned sp + -48)] WaF).
    { intros x Hx. unfold WaF in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
      split; [lia|]. split; [lia | exact I]. }
    pose proof (munch_trans WaF m m' m3 MU (munch_weaken _ WaF m' m3 SUBc MU3)) as MU4.
    pose proof (wmono_trans rsegs m m' m3 WM WM3) as WM4.
    pose proof (rw_cells_transport rsegs _ m' m3 _ _ FR MU3 WM3) as FR4.
    specialize (FR4 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (wr_at_transport rsegs m' m3 _ _ WO WM3) as WO4.
    pose proof (bytes_at_transport rsegs _ m' m3 _ _ BH MU3) as BH4.
    specialize (BH4 ltac:(rewrite LH; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m3 _ _ B5 MU3) as B54.
    specialize (B54 ltac:(rewrite LP5; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    destruct RW3 as [[_ BD3] _]. cbn [cells_bytes cbytes] in BD3. rewrite app_nil_r in BD3.
    clear FR WO BH B5 BD B20 MU WM MI ST MU3 WM3 AD' AO' AC SR.
    replace (ret_pc (Z_to_bv 64 0x86cdc)) with (Z_to_bv 64 0x86cdc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step. step. step. step.
    eapply inneraF with (k := (nn + 4)%nat) (i := 0%nat);
      [lia | lia | | | | eexists; exact FR4 | exact WO4 | | exact B54 | exact MU4 | exact WM4 | exact MI3 | exact ST3].
    - f_equal. lia.
    - f_equal. lia.
    - rewrite ?(unsigned_lit (bv_unsigned wn + 4)) by lia. rewrite bda_zext by lia. lia.
    - apply (bytes_at_cat _ _ _ (bv_unsigned wo + 20)); [exact BH4 | exact BD3 | rewrite LH; lia].
  Qed.

  (* +0x2c .. +0x234: the 20 header stores, each checked. *)
  Lemma midF : forall u0 u1 u2 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    ainvF m' [] ->
    evtF rsegs RNG QaF
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn wo wv wd x13 x14 x15 x16 x17
               s2 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x86ac0) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' PI.
    pose proof (zr_word wv) as Rv. unfold inr64 in Rv.
    chkF 0x86ac0 (bv_unsigned wo) 0 (Z_to_bv 5 13). astF 0.
    chkF 0x86adc (bv_unsigned wo + 1) 1 (Z_to_bv 5 14). astF 1.
    chkF 0x86af8 (bv_unsigned wo + 2) 2 (Z_to_bv 5 14). astF 2.
    chkF 0x86b10 (bv_unsigned wo + 3) 3 (Z_to_bv 5 14). astF 3.
    chkF 0x86b2c (bv_unsigned wo + 4) 4 (Z_to_bv 5 14). astF 4.
    chkF 0x86b44 (bv_unsigned wo + 5) 5 (Z_to_bv 5 14). astF 5.
    chkF 0x86b60 (bv_unsigned wo + 6) 6 (Z_to_bv 5 14). astF 6.
    chkF 0x86b78 (bv_unsigned wo + 7) 7 (Z_to_bv 5 14). astF 7.
    chkF 0x86b94 (bv_unsigned wo + 8) 8 (Z_to_bv 5 14). astF 8.
    chkF 0x86bb0 (bv_unsigned wo + 9) 9 (Z_to_bv 5 14). astF 9.
    chkF 0x86bcc (bv_unsigned wo + 10) 10 (Z_to_bv 5 14). astF 10.
    chkF 0x86be8 (bv_unsigned wo + 11) 11 (Z_to_bv 5 14). astF 11.
    chkF 0x86c04 (bv_unsigned wo + 12) 12 (Z_to_bv 5 14). astF 12.
    chkF 0x86c1c (bv_unsigned wo + 13) 13 (Z_to_bv 5 14). astF 13.
    chkF 0x86c34 (bv_unsigned wo + 14) 14 (Z_to_bv 5 14). astF 14.
    chkF 0x86c50 (bv_unsigned wo + 15) 15 (Z_to_bv 5 15). astF 15.
    chkF 0x86c68 (bv_unsigned wo + 16) 16 (Z_to_bv 5 13). astF 16.
    chkF 0x86c84 (bv_unsigned wo + 17) 17 (Z_to_bv 5 14). astF 17.
    chkF 0x86c9c (bv_unsigned wo + 18) 18 (Z_to_bv 5 14). astF 18.
    chkF 0x86cb8 (bv_unsigned wo + 19) 19 (Z_to_bv 5 14). astF 19.
    match goal with H : ainvF _ ?P |- _ =>
      assert (EH : P = dt1_hdr nn (bv_unsigned wv)); [|rewrite EH in H]
    end.
    { cbn [app]. unfold dt1_hdr, dt1_bytes. cbn [map].
      repeat apply rc_cons_eq;
        first [ reflexivity
              | apply Z_to_bv8_mod; rewrite unsigned_lit_wrap; rewrite mod_mod8_of_modw by lia;
                first [reflexivity | f_equal; lia] ]. }
    clear EH.
    eapply callpF; eassumption.
  Qed.
End BDAF.
End BDAFon.

Theorem build_dt1_single_F_holds_on :
  A.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on -> build_dt1_single_contract_F_on.
Proof.
  intros HMC. unfold build_dt1_single_contract_F_on, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo
    RBY RIMG RWIN RWS RRT ROUT RSO RDAT RSD.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ro. unfold inr64 in Ro.
  pose proof (zr_word a2) as Rd. unfold inr64 in Rd.
  pose proof (zr_word a3) as Rn. unfold inr64 in Rn.
  assert (Hsp : 2272 <= bv_unsigned sp) by (unfold HIGHMEM_BEG in HHM; lia).
  pose proof (bda_shadow_out m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HADo ltac:(lia)) as SO.
  pose proof (bda_rt_out (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HRTo ltac:(lia)) as RO.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 32 _ HADo SO) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 32 HADo) as HAD.
  pose proof (rt_asan_rt m _ HCE
                (fun x Hx => match Hx with
                             | or_introl H => RO x ltac:(unfold GOT_CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_introl H) => RO x ltac:(unfold CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_intror H) => SO x H
                             end)) as HRT.
  (* the two runtime cells are read at literal addresses: keep unfolded copies of their rng premises *)
  assert (RGz : rng RNG GOT_CELL_K 8)
    by (eapply rng_sub; [exact RRT | unfold GOT_CELL_K, RT_LO, RT_HI; lia | unfold GOT_CELL_K, RT_LO, RT_HI; lia]).
  assert (RCz : rng RNG CELL_K 8)
    by (eapply rng_sub; [exact RRT | unfold CELL_K, RT_LO, RT_HI; lia | unfold CELL_K, RT_LO, RT_HI; lia]).
  unfold GOT_CELL_K in RGz. unfold CELL_K in RCz.
  (* the three consequences of the two aligned shadow covers that the run uses *)
  assert (RSo1 : forall x, bv_unsigned a0 <= x <= bv_unsigned a0 + 31 -> rng RNG (x / 8 + ASAN_K) 1)
    by (intros x Hx; exact (bdaF_sh1 RNG ASAN_K _ _ x RSO Hx)).
  assert (RSoK : forall u v, bv_unsigned a0 <= u -> u <= v -> v <= bv_unsigned a0 + 31 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8))
    by (intros u v H1 H2 H3; exact (bdaF_shK RNG ASAN_K _ _ u v RSO H1 H2 H3)).
  assert (RSdK : forall u v, bv_unsigned a2 <= u -> u <= v -> v <= bv_unsigned a2 + bv_unsigned a3 - 1 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8)).
  { intros u v H1 H2 H3. destruct RSD as [E0 | RSD'];
      [exfalso; lia | exact (bdaF_shK RNG ASAN_K _ _ u v RSD' H1 H2 H3)]. }
  assert (RWSK : forall u v, bv_unsigned sp - 2272 <= u -> u <= v -> v <= bv_unsigned sp - 1 ->
                 rng RNG ((u / 8 + ASAN_K) / 8 * 8) ((v / 8 + ASAN_K) / 8 * 8 + 8 - (u / 8 + ASAN_K) / 8 * 8))
    by (intros u v H1 H2 H3;
        exact (bdaF_wincov RNG (bv_unsigned sp - 2272) 2272 u v RWS ltac:(lia) H1 H2 ltac:(lia))).
  clear RWS.
  set (off := ASAN_K) in HSR, HAD, HRT, RSo1. clearbody off.
  destruct HO as [[Hwf HOB] WO]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Lob _].
  cbn [cells_bytes cbytes cells_size csize Nat.add] in HOB, WO. rewrite app_nil_r in HOB.
  change (Z.of_nat 32) with 32 in WO.
  remember (Z.to_nat (bv_unsigned a3)) as nn eqn:Enn.
  assert (Hnn : Z.of_nat nn = bv_unsigned a3) by lia.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp);
                   (bv_unsigned a0, bv_unsigned a0 + 22 + bv_unsigned a3);
                   (bv_unsigned a0 + 31, bv_unsigned a0 + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  carve_frame 48%nat ST.
  step. step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  step. step. step. step. step.
  clear RG RC HRT HRT1.
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply BDAFon.midF; try eassumption; try lia.
  split; [eexists; eassumption|]. split; [assumption|]. split; [apply bytes_at_nil; lia|].
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. assumption.
Qed.

(* The narrowed contract from the narrowed footprint form (a Theorem Labs lane's step in build_dt1_single_c.v), from the same
   callee contract. *)
Theorem build_dt1_single_holds_of_F_on :
  A.Prog.asan_memcpy_cF_on.asan_memcpy_contract_F_on -> build_dt1_single_contract_on.
Proof. intros HMC. exact (build_dt1_single_contract_on_of_F_on (build_dt1_single_F_holds_on HMC)). Qed.

(* With no hypothesis left: the narrowed footprint statement at the footprint _on contract of __asan_memcpy that its
   owner proves for this image -- a Theorem Labs lane's asan_memcpy_holds_F_on (lib/A/Prog/asan_memcpyF_on.v). *)
Corollary build_dt1_single_F_holds_on_closed : build_dt1_single_contract_F_on.
Proof.
  exact (build_dt1_single_F_holds_on
           OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpyF_on.asan_memcpy_holds_F_on).
Qed.
