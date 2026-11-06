From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFPLib dt1_head_c asan_memcpy_c
  build_dt1_single_c.
Import ListNotations.
Open Scope Z_scope.

(* The ubsan proof (lib/U/Prog/build_dt1_single.v) with the checks of this build: the header is dt1_head
   (dt1_head_c.v), the copy of D is __asan_memcpy (asan_memcpy_c.v), and each load in the two sum loops and each of
   the 3 tail stores first reads the shadow byte of its address (s3 holds the shadow offset) and goes on when it is 0
   or above the address's offset in its 8-byte granule; addressable m o 32 gives that, so the __asan_report_* paths
   are not reached. The wrap checks (bgeu/bltu to unimp) are not taken, as in the ubsan build. *)

Lemma bdb_addr_app : forall m p n i, addressable m p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros m p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma bdb_app_mid : forall a t, app_mem a -> app_mem (a + 32) -> 0 <= t <= 32 -> app_mem (a + t).
Proof. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. intros a t H1 H2 Ht. lia. Qed.

Lemma bdb_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma bdb_shadow_out : forall m sp o n, HIGHMEM_BEG <= sp - 2272 -> addressable m o 32 -> 0 <= n <= 9 ->
  forall x, in_shadow x -> outside [(sp + -2272, sp); (o, o + 22 + n); (o + 31, o + 32)] x.
Proof.
  intros m sp o n Hs HA Hn x Hx.
  assert (NA : forall i, 0 <= i < 32 -> x <> o + i).
  { intros i Hi E. pose proof (bdb_addr_app m o 32 i HA Hi) as Ha. rewrite <- E in Ha.
    unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia. }
  cbn [outside].
  split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
  split; [intros H; apply (NA (x - o)); lia|].
  split; [intros H; apply (NA (x - o)); lia | exact I].
Qed.

Lemma bdb_rt_out : forall sp o n, HIGHMEM_BEG <= sp - 2272 -> (o + 32 <= RT_LO \/ RT_HI <= o) -> 0 <= n <= 9 ->
  forall x, RT_LO <= x < RT_HI -> outside [(sp + -2272, sp); (o, o + 22 + n); (o + 31, o + 32)] x.
Proof.
  intros sp o n Hs Ho Hn x Hx. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. cbn [outside].
  split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma bdb_neg : forall s, 0 <= s < 2^64 ->
  le1 (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 s))) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s Hs. rewrite (unsigned_lit s) by lia.
  unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma bdb_neg' : forall s, le1 (Z_to_bv 64 (0 - s)) = [Z_to_bv 8 ((- s) mod 256)].
Proof.
  intros s. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. rewrite mod_mod8_of_modw by lia. change (2^8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section BDB.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 J20 : list byte) (nn : nat) (off : Z).
  Hypothesis HDT : dt1_head_contract.
  Hypothesis HMC : asan_memcpy_contract.
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
  Definition Wb : list ivl :=
    [(bv_unsigned sp + -2272, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  (* The shadow bytes of the 32 bytes at o, read in m, with the offset off that s3 holds, and the two cells that
     give off. *)
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned wo) 32 Wb.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned wo) 32.
  Hypothesis HRT : asan_rt rsegs m GOT_CELL_K CELL_K off Wb.

  Definition Qb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch Wb m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp)
      /\ asan_cells m' /\ shadow_rw m'.

  Definition frb (m' : word -> option byte) : Prop :=
    exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma bdb_so : forall x, in_shadow x -> outside Wb x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bdb_shadow_out m (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HADo ltac:(lia)).
  Qed.

  Lemma bdb_ro : forall x, RT_LO <= x < RT_HI -> outside Wb x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bdb_rt_out (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HRTo ltac:(lia)).
  Qed.

  (* The runtime's cells and the shadow are outside Wb: a run that writes only Wb keeps them. *)
  Lemma bdb_rt : forall m', munch Wb m m' -> wmono rsegs m m' -> asan_cells m' /\ shadow_rw m'.
  Proof.
    intros m' MU WM. split.
    - exact (fl_asan_cells Wb m m' HCE MU bdb_ro).
    - exact (fl_shadow_rw Wb m m' HSW MU WM bdb_so).
  Qed.

  Lemma bdb_app_o : forall t, 0 <= t <= 32 -> app_mem (bv_unsigned wo + t).
  Proof.
    intros t Ht. apply bdb_app_mid; [|exact HAPo|exact Ht].
    pose proof (bdb_addr_app m _ 32 0 HADo ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
  Qed.

  (* dt1_head's footprint (its frame below sp - 48 and the 20 bytes at o) is inside Wb. *)
  Lemma bdb_sub_head : forall x, outside Wb x ->
    outside [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (bv_unsigned wo, bv_unsigned wo + 20)] x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    intros x Hx. unfold Wb in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
    split; [lia|]. split; [lia | exact I].
  Qed.

  (* The check of byte o + j in a memory m' that the run reached writing only Wb: the shadow byte k is readable and
     passes the check (0, or above X mod 8). *)
  Lemma bdb_shadow : forall m' X j, munch Wb m m' -> 0 <= j < 32 -> X = bv_unsigned wo + j ->
    exists k : byte, ov_read_bytes rsegs m' (wa (X / 8 + off)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros m' X j MU Hj ->.
    pose proof (asan_shadow_rd_munch rsegs m m' off _ 32 Wb Wb HSR MU (fun x Hx => Hx)) as HR'.
    pose proof (asan_addressable_munch rsegs m m' off _ 32 Wb Wb HAD HSR MU (fun x Hx => Hx)) as HA'.
    destruct (asan_shadow_read rsegs m' off _ 32 Wb j HR' Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HA' j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A store of one byte at o + j, 0 <= j < 32, inside Wb. *)
  Lemma ost : forall m' j (b : byte), 0 <= j < 32 -> inside Wb (bv_unsigned wo + j) 1 ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    frb (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch Wb m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
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

  Ltac bmu mc := lazymatch goal with MU : munch _ _ mc |- _ => constr:(MU) end.

  Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

  Ltac steps_to P :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; steps_to P
    end.

  (* The check at pc P (srli, add s3, lb, bnez; slow path andi, blt) of address X = o + j; the register r that the
     slow path's andi writes is generalized at the join. *)
  Ltac chk P X j r :=
    steps_to P;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let MU := bmu mc in
      let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
      destruct (bdb_shadow mc X j MU ltac:(lia) ltac:(lia)) as (k & RK & OK & KR);
      step;
      rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
      step; step; clear RK; step;
      unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
      lazymatch goal with
      | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ bjoin G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              bjoin G r ]
          | intros ?; simp_regs; clear OK KR ]
      end
    end.

  (* +0x174 .. +0x18c: the epilogue. *)
  Lemma epib : forall x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x875a4) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) HB MU WM MI ST.
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (stk_release rsegs m' _ _ _ ST FR ltac:(lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in ST' by lia.
    step. step. step. step. step. step. step.
    apply evt_done. unfold Qb. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST'|]. split; [exact AC | exact SR].
  Qed.

  (* +0x150 .. +0x170: the wrap check of o + 31, the check and store of the block check byte at o + 31. *)
  Lemma finb : forall u0 u1 u2 x9 x10 x11 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 x11 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87580) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x9 x10 x11 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO HB MU WM MI ST.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) 31) as PR. change (Z.of_nat 31) with 31 in PR.
    step. step.
    if_false.
    chk 0x8758c (bv_unsigned wo + 31) 31 (Z_to_bv 5 13).
    step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
    step.
    first [ rewrite (bdb_neg (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) by lia
          | rewrite (bdb_neg' (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) ].
    destruct (ost m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                ltac:(cbn [inside Wb]; right; right; left; split; lia) FR WO MU WM MI ST)
      as (FR' & WO' & MU' & WM' & MI' & ST' & B31).
    eapply epib; [exact FR' | | exact MU' | exact WM' | exact MI' | exact ST'].
    unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
    apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
  Qed.

  (* +0x118 .. +0x14c: the block sum loop over o .. o + 30, each load wrap-checked and shadow-checked. *)
  Lemma outerb : forall k i u0 u1 u2 x9 x10 x11 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    bv_unsigned x11 = 18446744073709551615 - bv_unsigned wo ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 x11 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) (Z_to_bv 64 (Z.of_nat i))
               (Z_to_bv 64 31) x15 x16 x17 x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87548) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x9 x10 x11 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk H11 FR WO HB MU WM MI ST; [lia|].
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x11) by (rewrite unsigned_lit by lia; lia).
    chk 0x87550 (bv_unsigned wo + Z.of_nat i) (Z.of_nat i) (Z_to_bv 5 16).
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      eapply finb; eassumption.
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.

  (* +0xbc .. +0x114: the wrap checks and the shadow checks of o + 20 + n and o + 21 + n, the record check byte and
     the byte 247 stored there. *)
  Lemma tailb : forall u0 u1 u2 x10 x11 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 x11 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4))) x13 x14 x15 x16 x17
               wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x874ec) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' FR WO Bhd B5 MU WM MI ST.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) as PR.
    step.
    rewrite (rc_swrap_small (bv_unsigned wn + 20)) by lia.
    step.
    rewrite (zb_lxor_ones (bv_unsigned wo)) by lia.
    step.
    rewrite rc_ltu_lit by lia.
    if_false.
    chk 0x874fc (bv_unsigned wo + (bv_unsigned wn + 20)) (bv_unsigned wn + 20) (Z_to_bv 5 14).
    step. step. step.
    rewrite (rc_swrap_small (bv_unsigned wn + 21)) by lia.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
    step.
    rewrite rc_le1_stamp.
    change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
    destruct (ost m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                ltac:(cbn [inside Wb]; right; left; split; lia) FR WO MU WM MI ST)
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
    step.
    rewrite rc_ltu_lit by lia.
    if_false.
    chk 0x87524 (bv_unsigned wo + (bv_unsigned wn + 21)) (bv_unsigned wn + 21) (Z_to_bv 5 13).
    step. step. step.
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
    step.
    rewrite rc_le1_lit.
    replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
    destruct (ost m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                ltac:(cbn [inside Wb]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1 ST1)
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
    step.
    eapply outerb with (k := 31%nat) (i := 0%nat);
      [lia | lia | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2 | exact ST2].
    - rewrite unsigned_lit by lia. reflexivity.
    - unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
      change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
        with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
  Qed.

  (* +0x80 .. +0xb8: the record sum loop over o + 16 .. o + 19 + n, each load wrap-checked and shadow-checked. *)
  Lemma innerb : forall k i u0 u1 u2 x10 x14 x15 x16 x17 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    bv_unsigned x14 = Z.of_nat nn + 4 ->
    bv_unsigned x15 = 18446744073709551615 - (bv_unsigned wo + 16) ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i))
               (Z_to_bv 64 (bv_unsigned wo + 16)) x14 x15 x16 x17
               wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x874b0) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x10 x14 x15 x16 x17 u3 u4 u5 u6 m' Hik Hk H14 H15 FR WO Bhd B5 MU WM MI ST; [lia|].
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    replace (bv_unsigned wo + 16 + Z.of_nat i) with (bv_unsigned wo + Z.of_nat i + 16) in RD by lia.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x15) by (rewrite unsigned_lit by lia; lia).
    chk 0x874b8 (bv_unsigned wo + 16 + Z.of_nat i) (16 + Z.of_nat i) (Z_to_bv 5 17).
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_w x14 (Z.of_nat nn + 4) (Z.of_nat i + 1) H14) by lia.
    destruct k as [|k].
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with (nn + 4)%nat by lia.
      step.
      eapply tailb; eassumption.
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.

  (* +0x44 .. +0x7c: after dt1_head, the wrap check of o + 20, the call __asan_memcpy(o + 20, d, n), the wrap check
     of o + 16, then the record sum loop. *)
  Lemma callb : forall u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv)) ->
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 -> bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    bytes_at rsegs m' (bv_unsigned wd) D ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x87474) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn x10 x11 x12 x13
               x14 x15 x16 x17 wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87474) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) WO BH B20 B5 BD MU WM MI ST.
    pose proof (dt1_hdr_length nn (bv_unsigned wv)) as LH.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable Wb m m' _ _ HADd MU bdb_so) as AD'.
    pose proof (fl_addressable Wb m m' _ _ HADo MU bdb_so) as AO'.
    pose proof HMC as HM. unfold asan_memcpy_contract in HM. cbv zeta in HM.
    step. step.
    if_false.
    step. step. step. step.
    eapply evt_cut.
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
      - apply (bdb_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - exact HEd.
      - right. replace (bv_unsigned wo + 20 + bv_unsigned wn) with (bv_unsigned wo + (20 + bv_unsigned wn)) by lia.
        apply bdb_app_o. lia.
      - destruct H7d as [H0 | H7]; [left; exact H0 | right; split; [exact H7|]].
        replace (bv_unsigned wo + 20 + 7) with (bv_unsigned wo + 27) by lia. apply bdb_app_o. lia.
      - lia.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - lia.
      - lia.
      - exact AC.
      - exact SR.
      - exact MI. }
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
                           (bv_unsigned sp + -48 - 2224, bv_unsigned sp + -48)] Wb).
    { intros x Hx. unfold Wb in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
      split; [lia|]. split; [lia | exact I]. }
    pose proof (munch_trans Wb m m' m3 MU (munch_weaken _ Wb m' m3 SUBc MU3)) as MU4.
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
    replace (ret_pc (Z_to_bv 64 0x8748c)) with (Z_to_bv 64 0x8748c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step.
    if_false.
    step. step. step. step. step. step. step.
    eapply innerb with (k := (nn + 4)%nat) (i := 0%nat);
      [lia | lia | | | eexists; exact FR4 | exact WO4 | | exact B54 | exact MU4 | exact WM4 | exact MI3 | exact ST3].
    - rewrite (unsigned_lit (bv_unsigned wn + 4)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (unsigned_lit ((bv_unsigned wn + 4) * 2^32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. lia.
    - rewrite (unsigned_lit (bv_unsigned wo + 16)) by lia. rewrite zb_lxor_ones by lia.
      rewrite unsigned_lit by lia. reflexivity.
    - apply (bytes_at_cat _ _ _ (bv_unsigned wo + 20)); [exact BH4 | exact BD3 | rewrite LH; lia].
  Qed.

  (* +0x18 .. +0x40: the shadow offset into s3, then dt1_head(o, 3, n + 13, v), which writes the 20-byte header. *)
  Lemma midb : forall u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 -> bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    bytes_at rsegs m' (bv_unsigned wd) D ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 s0 s1 wo wv wd wn x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87448) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) WO B20 B5 BD MU WM MI ST.
    pose proof (zr_word wv) as Rv. unfold inr64 in Rv.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable Wb m m' _ _ HADo MU bdb_so) as AO'.
    pose proof (asan_rt_munch rsegs m m' _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_rt_got_read rsegs m' _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m' _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step. step. step. step. step. step. step. step. step.
    clear RG RC HRT1.
    eapply evt_cut.
    { eapply HDT.
      all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia; try unfold DT1_HEAD_FRAME.
      - lia.
      - apply (wr_at_prefix _ _ _ 32); [exact WO | lia].
      - exact ST.
      - lia.
      - lia.
      - exact AC.
      - exact SR.
      - apply (bdb_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - intros x Hx. apply bdb_sub_head.
        destruct Hx as [Hx | [Hx | Hx]].
        + apply bdb_ro. unfold GOT_CELL_K, RT_LO, RT_HI in *. lia.
        + apply bdb_ro. unfold CELL_K, RT_LO, RT_HI in *. lia.
        + apply bdb_so. exact Hx. }
    intros ms' PO.
    destruct PO as (a0' & a1' & a2' & a4' & a5' & a6' & a7' & m2 & E & BH & MU2 & WM2 & MI2 & ST2).
    subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in MU2 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia.
    unfold DT1_HEAD_FRAME in MU2.
    replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wn + 13)))) with (Z.of_nat nn + 13) in BH
      by (rewrite rc_swrap_small by lia; rewrite unsigned_lit by lia; lia).
    change (bv_unsigned (Z_to_bv 64 3)) with 3 in BH.
    change (dt1_bytes 3 (Z.of_nat nn + 13) (bv_unsigned wv)) with (dt1_hdr nn (bv_unsigned wv)) in BH.
    pose proof (munch_trans Wb m m' m2 MU (munch_weaken _ Wb m' m2 bdb_sub_head MU2)) as MU4.
    pose proof (wmono_trans rsegs m m' m2 WM WM2) as WM4.
    pose proof (MI2 MI) as MI4.
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ FR MU2 WM2) as FR4.
    specialize (FR4 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (wr_at_transport rsegs m' m2 _ _ WO WM2) as WO4.
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ B20 MU2) as B204.
    specialize (B204 ltac:(rewrite LJ20; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ B5 MU2) as B54.
    specialize (B54 ltac:(rewrite LP5; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ BD MU2) as BD4.
    specialize (BD4 ltac:(rewrite HLD; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    clear FR WO B20 B5 BD MU WM MI MU2 WM2 MI2 AC SR AO'.
    replace (ret_pc (Z_to_bv 64 0x87474)) with (Z_to_bv 64 0x87474) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply callb; [eexists; exact FR4 | exact WO4 | exact BH | exact B204 | exact B54 | exact BD4 | exact MU4
                  | exact WM4 | exact MI4 | exact ST2].
  Qed.
End BDB.

Theorem build_dt1_single_holds : dt1_head_contract -> asan_memcpy_contract -> build_dt1_single_contract.
Proof.
  intros HDT HMC. unfold build_dt1_single_contract, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ro. unfold inr64 in Ro.
  pose proof (zr_word a2) as Rd. unfold inr64 in Rd.
  pose proof (zr_word a3) as Rn. unfold inr64 in Rn.
  assert (Hsp : 2272 <= bv_unsigned sp) by (unfold HIGHMEM_BEG in HHM; lia).
  pose proof (bdb_shadow_out m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HADo ltac:(lia)) as SO.
  pose proof (bdb_rt_out (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HRTo ltac:(lia)) as RO.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 32 _ HADo SO) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 32 HADo) as HAD.
  pose proof (rt_asan_rt m _ HCE
                (fun x Hx => match Hx with
                             | or_introl H => RO x ltac:(unfold GOT_CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_introl H) => RO x ltac:(unfold CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_intror H) => SO x H
                             end)) as HRT.
  set (off := ASAN_K) in HSR, HAD, HRT. clearbody off.
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
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply midb; try eassumption; try lia.
  eexists; eassumption.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; wave lead a Theorem Labs lane; a Theorem Labs lane's brief dt1-on-B): build_dt1_single_holds_on
   proves the _on twin (build_dt1_single_c.v) from the _on contracts of its two callees, dt1_head (dt1_head_c.v,
   premise-free) and __asan_memcpy (asan_memcpy_c_on.v). Image-B twin of A's (a working branch
   ec2ad5b4f4f, lib/A/Prog/build_dt1_single.v blob e7a7c3c2726, Module BDAon); image B's run has the extra callee
   dt1_head. The run is the one above. Module BDBon holds Section BDB again with these changes: HDT is dt1_head's _on
   contract, so its call (midb) no longer passes a shadow premise; HMC is the _on contract of __asan_memcpy; HSW is the
   region premise shadow_rw_on R m with R = build_dt1_single_shadow_R o d n; the shadow conjunct of Qb (given by bdb_rt)
   is the region transport (each region the caller holds in m it holds in m'), by B.ShadowRwOnK.fl_shadow_rw_on with
   bdb_so; at the call of __asan_memcpy (callb) its region at (o + 20, d, n) is R, carried from m to the memory of the
   call by bdb_rt. build_dt1_single_holds and every existing statement are unchanged (callee case: the old theorem
   keeps the old callee contracts, which do not give the _on ones).
   The transport lemma is a Theorem Labs lane's lib/B/ShadowRwOnK.v (a working branch 2bfdc5c22cd, blob
   cecf687f34d), the light file that Requires no MemNormTr / BzBridge, so this file and build_dt1_singleF.v stay
   Bz-free (build_dt1_single_F_closed.v's header). It replaces this lane's earlier local copy bdb_shadow_rw_on_keep
   (68e223499da), whose statement and script were byte-identical. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memcpy_c_on.

Module BDBon.
Section BDB.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (wo wv wd wn : word) (ob D P5 J20 : list byte) (nn : nat) (off : Z).
  Hypothesis HDT : dt1_head_contract_on.
  Hypothesis HMC : B.Prog.asan_memcpy_c_on.asan_memcpy_contract_on.
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
    B.ShadowRwOn.shadow_rw_on (build_dt1_single_shadow_R (bv_unsigned wo) (bv_unsigned wd) (bv_unsigned wn)) m.
  Hypothesis HADo : addressable m (bv_unsigned wo) 32.
  Hypothesis HADd : addressable m (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis HAPo : app_mem (bv_unsigned wo + 32).
  Hypothesis HEd : end_in_app (bv_unsigned wd) (bv_unsigned wn).
  Hypothesis H7d : bv_unsigned wn = 0 \/ app_mem (bv_unsigned wd + 7).
  Hypothesis HRTo : bv_unsigned wo + 32 <= RT_LO \/ RT_HI <= bv_unsigned wo.

  (* The contract's footprint. *)
  Definition Wb : list ivl :=
    [(bv_unsigned sp + -2272, bv_unsigned sp);
     (bv_unsigned wo, bv_unsigned wo + 22 + bv_unsigned wn);
     (bv_unsigned wo + 31, bv_unsigned wo + 32)].

  (* The shadow bytes of the 32 bytes at o, read in m, with the offset off that s3 holds, and the two cells that
     give off. *)
  Hypothesis HSR : asan_shadow_rd rsegs m off (bv_unsigned wo) 32 Wb.
  Hypothesis HAD : asan_addressable rsegs m off (bv_unsigned wo) 32.
  Hypothesis HRT : asan_rt rsegs m GOT_CELL_K CELL_K off Wb.

  Definition Qb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                      (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob)
      /\ psum (skipn 16 (dt1_out nn (bv_unsigned wv) D ob)) (nn + 5) mod 128 = 0
      /\ psum (dt1_out nn (bv_unsigned wv) D ob) 32 mod 256 = 0
      /\ munch Wb m m'
      /\ wmono rsegs m m'
      /\ mem_inv rsegs m'
      /\ stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp)
      /\ asan_cells m' /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').

  Definition frb (m' : word -> option byte) : Prop :=
    exists j, rw_cells rsegs m' (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma bdb_so : forall x, in_shadow x -> outside Wb x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bdb_shadow_out m (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HADo ltac:(lia)).
  Qed.

  Lemma bdb_ro : forall x, RT_LO <= x < RT_HI -> outside Wb x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    exact (bdb_rt_out (bv_unsigned sp) (bv_unsigned wo) (bv_unsigned wn) HHM HRTo ltac:(lia)).
  Qed.

  (* The runtime's cells and the shadow are outside Wb: a run that writes only Wb keeps the cells and each shadow
     region present in m. *)
  Lemma bdb_rt : forall m', munch Wb m m' -> wmono rsegs m m' ->
    asan_cells m' /\ (forall P : Z -> Prop, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m').
  Proof.
    intros m' MU WM. split.
    - exact (fl_asan_cells Wb m m' HCE MU bdb_ro).
    - intros P HP. exact (B.ShadowRwOnK.fl_shadow_rw_on P Wb m m' HP MU WM bdb_so).
  Qed.

  Lemma bdb_app_o : forall t, 0 <= t <= 32 -> app_mem (bv_unsigned wo + t).
  Proof.
    intros t Ht. apply bdb_app_mid; [|exact HAPo|exact Ht].
    pose proof (bdb_addr_app m _ 32 0 HADo ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H.
  Qed.

  (* dt1_head's footprint (its frame below sp - 48 and the 20 bytes at o) is inside Wb. *)
  Lemma bdb_sub_head : forall x, outside Wb x ->
    outside [(bv_unsigned sp + -48 - 16, bv_unsigned sp + -48); (bv_unsigned wo, bv_unsigned wo + 20)] x.
  Proof.
    pose proof (zr_word wn) as Rn. unfold inr64 in Rn.
    intros x Hx. unfold Wb in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
    split; [lia|]. split; [lia | exact I].
  Qed.

  (* The check of byte o + j in a memory m' that the run reached writing only Wb: the shadow byte k is readable and
     passes the check (0, or above X mod 8). *)
  Lemma bdb_shadow : forall m' X j, munch Wb m m' -> 0 <= j < 32 -> X = bv_unsigned wo + j ->
    exists k : byte, ov_read_bytes rsegs m' (wa (X / 8 + off)) 1 = Some [k]
                     /\ (bv_signed k = 0 \/ X mod 8 < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros m' X j MU Hj ->.
    pose proof (asan_shadow_rd_munch rsegs m m' off _ 32 Wb Wb HSR MU (fun x Hx => Hx)) as HR'.
    pose proof (asan_addressable_munch rsegs m m' off _ 32 Wb Wb HAD HSR MU (fun x Hx => Hx)) as HA'.
    destruct (asan_shadow_read rsegs m' off _ 32 Wb j HR' Hj) as (k & RK & BK).
    exists k. split; [exact RK|]. split; [exact (HA' j k Hj BK) | apply rc_byte_signed].
  Qed.

  (* A store of one byte at o + j, 0 <= j < 32, inside Wb. *)
  Lemma ost : forall m' j (b : byte), 0 <= j < 32 -> inside Wb (bv_unsigned wo + j) 1 ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 -> munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    frb (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
    wr_at rsegs (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) (bv_unsigned wo) 32 /\
    munch Wb m (write_to_mem m' (wa (bv_unsigned wo + j)) [b]) /\
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

  Ltac bmu mc := lazymatch goal with MU : munch _ _ mc |- _ => constr:(MU) end.

  Ltac bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

  Ltac steps_to P :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; steps_to P
    end.

  (* The check at pc P (srli, add s3, lb, bnez; slow path andi, blt) of address X = o + j; the register r that the
     slow path's andi writes is generalized at the join. *)
  Ltac chk P X j r :=
    steps_to P;
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      let MU := bmu mc in
      let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
      destruct (bdb_shadow mc X j MU ltac:(lia) ltac:(lia)) as (k & RK & OK & KR);
      step;
      rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
      step; step; clear RK; step;
      unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by lia;
      lazymatch goal with
      | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
          let G := fresh "G" in
          enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F B fc rv mm ro));
          [ let K0 := fresh "K0" in
            destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
            [ bjoin G r
            | step;
              rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
              step;
              rewrite (rc_lts_signed (X mod 8) (bv_signed k))
                by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); lia);
              replace (X mod 8 <? bv_signed k) with true
                by (symmetry; apply Z.ltb_lt; destruct OK; lia);
              bjoin G r ]
          | intros ?; simp_regs; clear OK KR ]
      end
    end.

  (* +0x174 .. +0x18c: the epilogue. *)
  Lemma epib : forall x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> bytes_at rsegs m' (bv_unsigned wo) (dt1_out nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x875a4) fc None m' (seg_rom rsegs)).
  Proof.
    intros x1 x8 x9 x18 x19 u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) HB MU WM MI ST.
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (stk_release rsegs m' _ _ _ ST FR ltac:(lia)) as ST'.
    cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -48 + Z.of_nat 48) with (bv_unsigned sp) in ST' by lia.
    step. step. step. step. step. step. step.
    apply evt_done. unfold Qb. do 15 eexists. exists m'.
    split; [reflexivity|].
    split; [exact HB|].
    split; [apply dt1_so128; exact HLD|].
    split; [apply dt1_so256; assumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST'|]. split; [exact AC | exact SR].
  Qed.

  (* +0x150 .. +0x170: the wrap check of o + 31, the check and store of the block check byte at o + 31. *)
  Lemma finb : forall u0 u1 u2 x9 x10 x11 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 x11 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87580) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x9 x10 x11 x13 x14 x15 x16 x17 x18 u3 u4 u5 u6 m' FR WO HB MU WM MI ST.
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) 31) as PR. change (Z.of_nat 31) with 31 in PR.
    step. step.
    if_false.
    chk 0x8758c (bv_unsigned wo + 31) 31 (Z_to_bv 5 13).
    step.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 31 1 WO ltac:(lia) ltac:(lia)) as HS.
    step.
    first [ rewrite (bdb_neg (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) by lia
          | rewrite (bdb_neg' (psum (dt1_body nn (bv_unsigned wv) D ob) 31)) ].
    destruct (ost m' 31 (Z_to_bv 8 ((- psum (dt1_body nn (bv_unsigned wv) D ob) 31) mod 256)) ltac:(lia)
                ltac:(cbn [inside Wb]; right; right; left; split; lia) FR WO MU WM MI ST)
      as (FR' & WO' & MU' & WM' & MI' & ST' & B31).
    eapply epib; [exact FR' | | exact MU' | exact WM' | exact MI' | exact ST'].
    unfold dt1_out. eapply bytes_at_cat; [ | exact B31 | rewrite LB; lia].
    apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | rewrite LB; cbn [length]; lia].
  Qed.

  (* +0x118 .. +0x14c: the block sum loop over o .. o + 30, each load wrap-checked and shadow-checked. *)
  Lemma outerb : forall k i u0 u1 u2 x9 x10 x11 x15 x16 x17 x18 u3 u4 u5 u6 m',
    (i + k = 31)%nat -> (0 < k)%nat ->
    bv_unsigned x11 = 18446744073709551615 - bv_unsigned wo ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_body nn (bv_unsigned wv) D ob) ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo x9
               x10 x11 (Z_to_bv 64 (psum (dt1_body nn (bv_unsigned wv) D ob) i)) (Z_to_bv 64 (Z.of_nat i))
               (Z_to_bv 64 31) x15 x16 x17 x18 (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87548) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x9 x10 x11 x15 x16 x17 x18 u3 u4 u5 u6 m' Hik Hk H11 FR WO HB MU WM MI ST; [lia|].
    pose proof (dt1_body_length nn (bv_unsigned wv) D ob HLD Lob Hn9) as LB.
    pose proof (rd_byte rsegs m' (bv_unsigned wo) _ i HB ltac:(lia)) as RD.
    pose proof (psum_range (dt1_body nn (bv_unsigned wv) D ob) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x11) by (rewrite unsigned_lit by lia; lia).
    chk 0x87550 (bv_unsigned wo + Z.of_nat i) (Z.of_nat i) (Z_to_bv 5 16).
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (Z.of_nat i + 1) 31) by lia.
    destruct k as [|k].
    - replace (Z.of_nat i + 1 =? 31) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with 31%nat by lia.
      step.
      eapply finb; eassumption.
    - replace (Z.of_nat i + 1 =? 31) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.

  (* +0xbc .. +0x114: the wrap checks and the shadow checks of o + 20 + n and o + 21 + n, the record check byte and
     the byte 247 stored there. *)
  Lemma tailb : forall u0 u1 u2 x10 x11 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 x11 (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4))) x13 x14 x15 x16 x17
               wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x874ec) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' FR WO Bhd B5 MU WM MI ST.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    assert (LHD : length (dt1_hdr nn (bv_unsigned wv) ++ D) = (20 + nn)%nat)
      by (rewrite length_app, dt1_hdr_length, HLD; lia).
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) as PR.
    step.
    rewrite (rc_swrap_small (bv_unsigned wn + 20)) by lia.
    step.
    rewrite (zb_lxor_ones (bv_unsigned wo)) by lia.
    step.
    rewrite rc_ltu_lit by lia.
    if_false.
    chk 0x874fc (bv_unsigned wo + (bv_unsigned wn + 20)) (bv_unsigned wn + 20) (Z_to_bv 5 14).
    step. step. step.
    rewrite (rc_swrap_small (bv_unsigned wn + 21)) by lia.
    pose proof (wr_at_store_ok rsegs m' (bv_unsigned wo) 32 (bv_unsigned wn + 20) 1 WO ltac:(lia) ltac:(lia)) as HS1.
    step.
    rewrite rc_le1_stamp.
    change ((- psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) (nn + 4)) mod 128) with (dt1_ick nn (bv_unsigned wv) D).
    destruct (ost m' (bv_unsigned wn + 20) (Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)) ltac:(lia)
                ltac:(cbn [inside Wb]; right; left; split; lia) FR WO MU WM MI ST)
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
    step.
    rewrite rc_ltu_lit by lia.
    if_false.
    chk 0x87524 (bv_unsigned wo + (bv_unsigned wn + 21)) (bv_unsigned wn + 21) (Z_to_bv 5 13).
    step. step. step.
    pose proof (wr_at_store_ok rsegs m1 (bv_unsigned wo) 32 (bv_unsigned wn + 21) 1 WO1 ltac:(lia) ltac:(lia)) as HS2.
    step.
    rewrite rc_le1_lit.
    replace (Z_to_bv 8 (-9)) with (Z_to_bv 8 247) by (apply Z_to_bv8_mod; reflexivity).
    destruct (ost m1 (bv_unsigned wn + 21) (Z_to_bv 8 247) ltac:(lia)
                ltac:(cbn [inside Wb]; right; left; split; lia) FR1 WO1 MU1 WM1 MI1 ST1)
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
    step.
    eapply outerb with (k := 31%nat) (i := 0%nat);
      [lia | lia | | exact FR2 | exact WO2 | | exact MU2 | exact WM2 | exact MI2 | exact ST2].
    - rewrite unsigned_lit by lia. reflexivity.
    - unfold dt1_body. rewrite <- EP5. rewrite app_assoc.
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 20))); [exact Bhd2 | | rewrite LHD; lia].
      change ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D); Z_to_bv 8 247] ++ P5)
        with ([Z_to_bv 8 (dt1_ick nn (bv_unsigned wv) D)] ++ ([Z_to_bv 8 247] ++ P5)).
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + (bv_unsigned wn + 21))); [exact Bick2 | | cbn [length]; lia].
      apply (bytes_at_cat _ _ _ (bv_unsigned wo + 22 + bv_unsigned wn)); [exact Bf7 | exact B52 | cbn [length]; lia].
  Qed.

  (* +0x80 .. +0xb8: the record sum loop over o + 16 .. o + 19 + n, each load wrap-checked and shadow-checked. *)
  Lemma innerb : forall k i u0 u1 u2 x10 x14 x15 x16 x17 u3 u4 u5 u6 m',
    (i + k = nn + 4)%nat -> (0 < k)%nat ->
    bv_unsigned x14 = Z.of_nat nn + 4 ->
    bv_unsigned x15 = 18446744073709551615 - (bv_unsigned wo + 16) ->
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv) ++ D) ->
    bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x8748c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn
               x10 (Z_to_bv 64 (Z.of_nat i)) (Z_to_bv 64 (psum (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i))
               (Z_to_bv 64 (bv_unsigned wo + 16)) x14 x15 x16 x17
               wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x874b0) fc None m' (seg_rom rsegs)).
  Proof.
    induction k as [|k IH];
      intros i u0 u1 u2 x10 x14 x15 x16 x17 u3 u4 u5 u6 m' Hik Hk H14 H15 FR WO Bhd B5 MU WM MI ST; [lia|].
    pose proof (bytes_at_skip16 rsegs m' _ _ D (dt1_hdr_length nn (bv_unsigned wv)) Bhd) as B16.
    assert (L4D : length (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) = (4 + nn)%nat)
      by (rewrite length_app, dt1_s4_length, HLD; lia).
    pose proof (rd_byte rsegs m' (bv_unsigned wo + 16) _ i B16 ltac:(lia)) as RD.
    replace (bv_unsigned wo + 16 + Z.of_nat i) with (bv_unsigned wo + Z.of_nat i + 16) in RD by lia.
    pose proof (psum_range (skipn 16 (dt1_hdr nn (bv_unsigned wv)) ++ D) i) as PR.
    step.
    rewrite (rc_ltu_ge (Z_to_bv 64 (Z.of_nat i)) x15) by (rewrite unsigned_lit by lia; lia).
    chk 0x874b8 (bv_unsigned wo + 16 + Z.of_nat i) (16 + Z.of_nat i) (Z_to_bv 5 17).
    step. step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_w x14 (Z.of_nat nn + 4) (Z.of_nat i + 1) H14) by lia.
    destruct k as [|k].
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota.
      replace (S i) with (nn + 4)%nat by lia.
      step.
      eapply tailb; eassumption.
    - replace (Z.of_nat nn + 4 =? Z.of_nat i + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      apply (IH (S i)); first [lia | assumption].
  Qed.

  (* +0x44 .. +0x7c: after dt1_head, the wrap check of o + 20, the call __asan_memcpy(o + 20, d, n), the wrap check
     of o + 16, then the record sum loop. *)
  Lemma callb : forall u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo) (dt1_hdr nn (bv_unsigned wv)) ->
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 -> bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    bytes_at rsegs m' (bv_unsigned wd) D ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR (Z_to_bv 64 0x87474) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 wo wn x10 x11 x12 x13
               x14 x15 x16 x17 wd (Z_to_bv 64 off) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87474) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x10 x11 x12 x13 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) WO BH B20 B5 BD MU WM MI ST.
    pose proof (dt1_hdr_length nn (bv_unsigned wv)) as LH.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable Wb m m' _ _ HADd MU bdb_so) as AD'.
    pose proof (fl_addressable Wb m m' _ _ HADo MU bdb_so) as AO'.
    pose proof HMC as HM. unfold B.Prog.asan_memcpy_c_on.asan_memcpy_contract_on in HM. cbv zeta in HM.
    step. step.
    if_false.
    step. step. step. step.
    eapply evt_cut.
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
      - apply (bdb_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - exact HEd.
      - right. replace (bv_unsigned wo + 20 + bv_unsigned wn) with (bv_unsigned wo + (20 + bv_unsigned wn)) by lia.
        apply bdb_app_o. lia.
      - destruct H7d as [H0 | H7]; [left; exact H0 | right; split; [exact H7|]].
        replace (bv_unsigned wo + 20 + 7) with (bv_unsigned wo + 27) by lia. apply bdb_app_o. lia.
      - lia.
      - lia.
      - lia.
      - exact ST.
      - lia.
      - lia.
      - lia.
      - exact AC.
      - (* the region of __asan_memcpy at (o + 20, d, n) is R, present in m' by bdb_rt *)
        apply (B.ShadowRwOn.shadow_rw_on_mono
                 (build_dt1_single_shadow_R (bv_unsigned wo) (bv_unsigned wd) (bv_unsigned wn)));
          [|exact (SR _ HSW)].
        intros a Ha. unfold B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Ha.
        rewrite ?(unsigned_lit (bv_unsigned wo + 20)) in Ha by lia. exact Ha.
      - exact MI. }
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
                           (bv_unsigned sp + -48 - 2224, bv_unsigned sp + -48)] Wb).
    { intros x Hx. unfold Wb in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & H2 & H3 & _).
      split; [lia|]. split; [lia | exact I]. }
    pose proof (munch_trans Wb m m' m3 MU (munch_weaken _ Wb m' m3 SUBc MU3)) as MU4.
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
    replace (ret_pc (Z_to_bv 64 0x8748c)) with (Z_to_bv 64 0x8748c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    step. step.
    if_false.
    step. step. step. step. step. step. step.
    eapply innerb with (k := (nn + 4)%nat) (i := 0%nat);
      [lia | lia | | | eexists; exact FR4 | exact WO4 | | exact B54 | exact MU4 | exact WM4 | exact MI3 | exact ST3].
    - rewrite (unsigned_lit (bv_unsigned wn + 4)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (unsigned_lit ((bv_unsigned wn + 4) * 2^32)) by lia. rewrite Z.shiftr_div_pow2 by lia.
      rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. lia.
    - rewrite (unsigned_lit (bv_unsigned wo + 16)) by lia. rewrite zb_lxor_ones by lia.
      rewrite unsigned_lit by lia. reflexivity.
    - apply (bytes_at_cat _ _ _ (bv_unsigned wo + 20)); [exact BH4 | exact BD3 | rewrite LH; lia].
  Qed.

  (* +0x18 .. +0x40: the shadow offset into s3, then dt1_head(o, 3, n + 13, v), which writes the 20-byte header. *)
  Lemma midb : forall u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m',
    frb m' -> wr_at rsegs m' (bv_unsigned wo) 32 ->
    bytes_at rsegs m' (bv_unsigned wo + 20) J20 -> bytes_at rsegs m' (bv_unsigned wo + 22 + bv_unsigned wn) P5 ->
    bytes_at rsegs m' (bv_unsigned wd) D ->
    munch Wb m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
    stk rsegs m' (bv_unsigned sp + -2272) (bv_unsigned sp + -48) ->
    evt rsegs Qb
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 s0 s1 wo wv wd wn x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x87448) fc None m' (seg_rom rsegs)).
  Proof.
    intros u0 u1 u2 x14 x15 x16 x17 u3 u4 u5 u6 m' (jk & FR) WO B20 B5 BD MU WM MI ST.
    pose proof (zr_word wv) as Rv. unfold inr64 in Rv.
    assert (LP5 : length P5 = (9 - nn)%nat) by (rewrite EP5, length_firstn, length_skipn; lia).
    destruct (bdb_rt m' MU WM) as [AC SR].
    pose proof (fl_addressable Wb m m' _ _ HADo MU bdb_so) as AO'.
    pose proof (asan_rt_munch rsegs m m' _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
    pose proof (asan_rt_got_read rsegs m' _ _ off _ HRT1) as RG.
    pose proof (asan_rt_cell_read rsegs m' _ _ off _ HRT1) as RC.
    unfold GOT_CELL_K, CELL_K in RG, RC.
    step. step. step. step. step. step. step. step. step. step. step.
    clear RG RC HRT1.
    eapply evt_cut.
    { eapply HDT.
      all: rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia; try unfold DT1_HEAD_FRAME.
      - lia.
      - apply (wr_at_prefix _ _ _ 32); [exact WO | lia].
      - exact ST.
      - lia.
      - lia.
      - exact AC.
      - apply (bdb_addr_sub m' (bv_unsigned wo) 32); [exact AO' | lia | lia | lia].
      - intros x Hx. apply bdb_sub_head.
        destruct Hx as [Hx | [Hx | Hx]].
        + apply bdb_ro. unfold GOT_CELL_K, RT_LO, RT_HI in *. lia.
        + apply bdb_ro. unfold CELL_K, RT_LO, RT_HI in *. lia.
        + apply bdb_so. exact Hx. }
    intros ms' PO.
    destruct PO as (a0' & a1' & a2' & a4' & a5' & a6' & a7' & m2 & E & BH & MU2 & WM2 & MI2 & ST2).
    subst ms'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in MU2 by lia.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia.
    unfold DT1_HEAD_FRAME in MU2.
    replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (bv_unsigned wn + 13)))) with (Z.of_nat nn + 13) in BH
      by (rewrite rc_swrap_small by lia; rewrite unsigned_lit by lia; lia).
    change (bv_unsigned (Z_to_bv 64 3)) with 3 in BH.
    change (dt1_bytes 3 (Z.of_nat nn + 13) (bv_unsigned wv)) with (dt1_hdr nn (bv_unsigned wv)) in BH.
    pose proof (munch_trans Wb m m' m2 MU (munch_weaken _ Wb m' m2 bdb_sub_head MU2)) as MU4.
    pose proof (wmono_trans rsegs m m' m2 WM WM2) as WM4.
    pose proof (MI2 MI) as MI4.
    pose proof (rw_cells_transport rsegs _ m' m2 _ _ FR MU2 WM2) as FR4.
    specialize (FR4 ltac:(simpl_sizes; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (wr_at_transport rsegs m' m2 _ _ WO WM2) as WO4.
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ B20 MU2) as B204.
    specialize (B204 ltac:(rewrite LJ20; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ B5 MU2) as B54.
    specialize (B54 ltac:(rewrite LP5; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    pose proof (bytes_at_transport rsegs _ m' m2 _ _ BD MU2) as BD4.
    specialize (BD4 ltac:(rewrite HLD; cbn [disjoint_from]; split; [lia|]; split; [lia | exact I])).
    clear FR WO B20 B5 BD MU WM MI MU2 WM2 MI2 AC SR AO'.
    replace (ret_pc (Z_to_bv 64 0x87474)) with (Z_to_bv 64 0x87474) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    eapply callb; [eexists; exact FR4 | exact WO4 | exact BH | exact B204 | exact B54 | exact BD4 | exact MU4
                  | exact WM4 | exact MI4 | exact ST2].
  Qed.
End BDB.
End BDBon.

Theorem build_dt1_single_holds_on :
  dt1_head_contract_on -> B.Prog.asan_memcpy_c_on.asan_memcpy_contract_on -> build_dt1_single_contract_on.
Proof.
  intros HDT HMC. unfold build_dt1_single_contract_on, BUILD_DT1_SINGLE, BUILD_DT1_SINGLE_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ob D ST Hn Ho0 Ho32 HO Hd HLD HD DdO DfO Dfd MI HCE HSW HHM HAE HADo HADd HAPo HEd H7d HRTo.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ro. unfold inr64 in Ro.
  pose proof (zr_word a2) as Rd. unfold inr64 in Rd.
  pose proof (zr_word a3) as Rn. unfold inr64 in Rn.
  assert (Hsp : 2272 <= bv_unsigned sp) by (unfold HIGHMEM_BEG in HHM; lia).
  pose proof (bdb_shadow_out m (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HADo ltac:(lia)) as SO.
  pose proof (bdb_rt_out (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a3) HHM HRTo ltac:(lia)) as RO.
  pose proof (rt_shadow_rd m (bv_unsigned a0) 32 _ HADo SO) as HSR.
  pose proof (rt_addressable m (bv_unsigned a0) 32 HADo) as HAD.
  pose proof (rt_asan_rt m _ HCE
                (fun x Hx => match Hx with
                             | or_introl H => RO x ltac:(unfold GOT_CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_introl H) => RO x ltac:(unfold CELL_K, RT_LO, RT_HI in *; lia)
                             | or_intror (or_intror H) => SO x H
                             end)) as HRT.
  set (off := ASAN_K) in HSR, HAD, HRT. clearbody off.
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
  pose proof (bytes_at_sub rsegs _ _ ob 20 nn HOB ltac:(lia)) as B20.
  pose proof (bytes_at_sub rsegs _ _ ob (22 + nn) (9 - nn) HOB ltac:(lia)) as B5.
  remember (firstn nn (skipn 20 ob)) as J20 eqn:EJ20.
  assert (LJ20 : length J20 = nn) by (subst J20; rewrite length_firstn, length_skipn; lia).
  clear EJ20.
  remember (firstn (9 - nn) (skipn (22 + nn) ob)) as P5 eqn:EP5.
  change (Z.of_nat 20) with 20 in B20.
  apply (bytes_at_addr _ _ _ (bv_unsigned a0 + 22 + bv_unsigned a3)) in B5; [|lia].
  clear HOB.
  eapply BDBon.midb; try eassumption; try lia.
  eexists; eassumption.
Qed.
