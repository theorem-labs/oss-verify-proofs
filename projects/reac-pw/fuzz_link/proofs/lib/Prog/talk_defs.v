(* talk (fuzz_link.c:333-384), PLAIN build: the pieces of the walk of lib/Prog/talk_c.v.

   The code (link/ct/dis/plain/talk.s, 0x156e4, 964 bytes) is walked in fragments. Each fragment
   is stated here as a Prop in continuation form: for ANY goal Q, if Q is reachable from every
   state the fragment can leave by, it is reachable from the fragment's entry state. A fragment
   names only the registers and memory it reads; every other register is carried through
   unchanged, and the registers it clobbers are free in the continuation.

     F_exit      0x1584c          the epilogue: the 13 saved registers back, sp + 144, ret
     F_msg       0x1580c          the message loop of one chunk (link_spec msg_scan)
     F_chunk     0x157d0          the chunk loop (chunk_loop), with the store of the cursor
     F_attr      0x158f4          the attribute loop of the first RTM_NEWLINK (attr_scan)
     F_kind      0x159ac          the IFLA_INFO_* loop inside one IFLA_LINKINFO (kind_scan)
     F_take_al   0x1593c          take_text of an IFLA_IFALIAS into the alias buffer
     F_take_kd   0x159e4          take_text of an IFLA_INFO_KIND into the kind buffer

   The stack frame is [SP-144, SP). The prologue stores the 13 saved registers at [SP-104, SP);
   the RTM_NEWLINK arm stores five words at [SP-144, SP-104): alias_n - 1, the alias flag,
   b + 4 (b the chunk base), kind_n - 1, the kind flag. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Local Open Scope Z_scope.

Definition tG : Z := A_G_NL.

(* the flag the arm spills: buffer non-NULL and cap non-zero *)
Definition flagz (p n : Z) : Z := if (p =? 0) || (n =? 0) then 0 else 1.

(* the width of a buffer the code may write: none when the pointer is NULL (take_text returns at
   once, fuzz_link.c:321), else its cap *)
Definition bw (p n : Z) : Z := if p =? 0 then 0 else n.

(* the code a chunk answers when it stops the exchange without filling the buffers *)
Definition msg_ret (v : nlv) (rc : Z) : Prop :=
  (v = NlShort /\ rc = - E_IO) \/ (exists code, v = NlErr code /\ rc = norm_rc code) \/
  (v = NlLink no_attrs /\ rc = 0).

(* the model block after a store of the cursor *)
Definition md_set_next (mb : list byte) (j : Z) : list byte := upd_bytes mb 8 (le4 (Z_to_bv 64 j)).

(* the two text buffers hold what the attributes seen so far put there, and stay writable *)
Definition bufs (m : word -> option byte) (acc : attrs) (KD KN AD AN : Z) : Prop :=
  (KD <> 0 -> 1 <= KN -> exists j, rw_cells rsegs m KD [CB (Z.to_nat KN) j]) /\
  (AD <> 0 -> 1 <= AN -> exists j, rw_cells rsegs m AD [CB (Z.to_nat AN) j]) /\
  (forall pay, a_kind acc = Some pay -> KD <> 0 -> 1 <= KN -> cstr_at m KD (cut_text pay KN)) /\
  (forall pay, a_alias acc = Some pay -> AD <> 0 -> 1 <= AN -> cstr_at m AD (cut_text pay AN)).

(* each live buffer is apart from the chunk [B, B+n), from the frame, and from the other *)
Definition bufsep (B n SP KD KN AD AN : Z) : Prop :=
  (KD <> 0 -> 1 <= KN -> apart KD KN B n /\ apart KD KN (SP + -144) 144) /\
  (AD <> 0 -> 1 <= AN -> apart AD AN B n /\ apart AD AN (SP + -144) 144) /\
  (KD <> 0 -> 1 <= KN -> AD <> 0 -> 1 <= AN -> apart KD KN AD AN).

(* the five words the RTM_NEWLINK arm spills at [SP-144, SP-104) *)
Definition spill_cells (AN B KN AD KD : Z) : list cell :=
  [C8 (Z_to_bv 64 (AN - 1)); C8 (Z_to_bv 64 (flagz AD AN)); C8 (Z_to_bv 64 (B + 4));
   C8 (Z_to_bv 64 (KN - 1)); C8 (Z_to_bv 64 (flagz KD KN))].

(* the 13 words the prologue saves at [SP-104, SP) *)
Definition saved_cells (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) : list cell :=
  [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 S2; C8 S1; C8 S0; C8 RA].

(* ==========================================================================
   F_exit, 0x1584c: ld ra .. s11 from [SP-104, SP), addi sp, sp, 0x90, ret
   ========================================================================== *)
Definition F_exit_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP : Z)
    (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word),
  sp = Z_to_bv 64 (SP + -144) -> 144 <= SP < 2 ^ 64 ->
  rw_cells rsegs m (SP + -104) (saved_cells RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11) ->
  Q (MS (mkR RA (Z_to_bv 64 SP) gp tp t0 t1 t2 S0 S1 a0 a1 a2 a3 a4 a5 a6 a7
             S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
        F (ret_pc RA) fc None m (seg_rom rsegs)) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1584c) fc None m (seg_rom rsegs)).

(* ==========================================================================
   F_msg, 0x1580c: the message loop over one chunk `ck` at B (a7 = off, t0 = left).
   Leaves by 0x157f0 (the walk ended: next chunk), by 0x1584c (an NLMSG_ERROR, or an
   RTM_NEWLINK too short to hold an attribute) or by 0x158a0 (an RTM_NEWLINK of ml >= 36).
   ========================================================================== *)
Definition F_msg_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (fu : nat) (off left : Z),
  a4 = Z_to_bv 64 16 -> a6 = Z_to_bv 64 2 -> s6 = Z_to_bv 64 B ->
  a7 = Z_to_bv 64 off -> t0 = Z_to_bv 64 left ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= off -> off + left = Z.of_nat (length ck) -> 16 <= left -> left < Z.of_nat fu ->
  (msg_scan fu ck off left = NlNone ->
     forall t0' t1' t2' a7' s7',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1 a2 a3 a4 a5 a6 a7' s2 s3 s4 s5 s6 s7' s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x157f0) fc None m (seg_rom rsegs))) ->
  (forall rc, msg_ret (msg_scan fu ck off left) rc ->
     forall t0' t1' t2' a1' a2' a3' a7' s7',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rc) a1' a2' a3' a4 a5 a6 a7'
                s2 s3 s4 s5 s6 s7' s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1584c) fc None m (seg_rom rsegs))) ->
  (forall f' off' ml,
     msg_scan fu ck off left
       = NlLink (attr_scan f' ck (off' + NL_HDR + IFI_LEN) (ml - NL_HDR - IFI_LEN) no_attrs) ->
     36 <= ml -> 0 <= off' -> off' + ml <= Z.of_nat (length ck) -> ml - 32 < Z.of_nat f' ->
     forall t0' t1' t2' a0',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1 a2 a3 a4 a5 a6 (Z_to_bv 64 off')
                s2 s3 s4 s5 s6 (Z_to_bv 64 ml) s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x158a0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1580c) fc None m (seg_rom rsegs)).

(* ==========================================================================
   F_chunk, 0x157d0: the chunk loop head with a1 = c < n_chunks. Each turn stores c+1 into the
   model's cursor (M+8). Leaves by 0x1584c (rc) or by 0x158a0 (an RTM_NEWLINK of ml >= 36 in
   chunk c').
   ========================================================================== *)
Definition F_chunk_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (M : Z) (kbs mb : list byte) (fu : nat) (c : Z),
  a0 = Z_to_bv 64 0x40000 -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 (tG + 0x40000) ->
  a3 = Z_to_bv 64 tG -> a4 = Z_to_bv 64 16 -> a5 = Z_to_bv 64 4096 -> a6 = Z_to_bv 64 2 ->
  s4 = Z_to_bv 64 M -> s5 = Z_to_bv 64 (tG + 4096 * c + 4) ->
  nlk_at m kbs -> nlk_wf kbs -> model_at m M mb -> apart_gnl M MD_SIZE -> mem_inv rsegs m ->
  0 <= c < nk_n_chunks kbs -> nk_n_chunks kbs - c < Z.of_nat fu ->
  (forall rc v j m',
     chunk_loop fu (nk_chunks kbs) (Z.to_nat c) = (v, j) ->
     (v = NlNone /\ rc = - nk_end_errno kbs) \/ msg_ret v rc ->
     munch [(M + 8, M + 12)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     model_at m' M (md_set_next mb (Z.of_nat j)) ->
     forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 rc) a1' a2' a3' a4' a5' a6' a7'
                s2 s3 s4 s5' s6' s7' s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1584c) fc None m' (seg_rom rsegs))) ->
  (forall c' f' off' ml m',
     chunk_loop fu (nk_chunks kbs) (Z.to_nat c)
       = (NlLink (attr_scan f' (nk_chunk kbs c') (off' + NL_HDR + IFI_LEN) (ml - NL_HDR - IFI_LEN)
                            no_attrs), S (Z.to_nat c')) ->
     c <= c' < nk_n_chunks kbs ->
     36 <= ml -> 0 <= off' -> off' + ml <= Z.of_nat (length (nk_chunk kbs c')) ->
     ml - 32 < Z.of_nat f' ->
     munch [(M + 8, M + 12)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     model_at m' M (md_set_next mb (c' + 1)) ->
     forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6',
     evt rsegs Q
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' (Z_to_bv 64 off')
                s2 s3 s4 (Z_to_bv 64 (tG + 4096 * c' + 4)) (Z_to_bv 64 (tG + 4096 * c'))
                (Z_to_bv 64 ml) s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x158a0) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x157d0) fc None m (seg_rom rsegs)).

(* ==========================================================================
   F_take_al, 0x1593c (after the alias flag test): take_text of the IFLA_IFALIAS at offset a
   (length l) of chunk ck into the alias buffer AD (cap AN). Ends at 0x15a54 (the step to the
   next attribute) with a4 = 4, a5 = 1, a6 = 3 set again after the memcpy.
   F_take_kd, 0x159e4 (after the kind flag test): the same for the IFLA_INFO_KIND at offset i
   (length li) into the kind buffer KD (cap KN). Ends at 0x15a40.
   ========================================================================== *)
Definition F_take_al_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (a l SP KD KN AD AN : Z) (jk : list byte),
  s4 = Z_to_bv 64 l -> s11 = Z_to_bv 64 a -> s5 = Z_to_bv 64 (B + 4) -> s0 = Z_to_bv 64 AD ->
  sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= a -> 4 <= l -> a + l <= Z.of_nat (length ck) ->
  AD <> 0 -> 1 <= AN -> rw_cells rsegs m AD [CB (Z.to_nat AN) jk] ->
  apart AD AN B (Z.of_nat (length ck)) -> apart AD AN (SP + -144) 144 ->
  mem_inv rsegs m ->
  (forall m',
     munch [(AD, AD + AN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     cstr_at m' AD (cut_text (slice ck (a + RTA_HDR) (l - RTA_HDR)) AN) ->
     (exists j, rw_cells rsegs m' AD [CB (Z.to_nat AN) j]) ->
     forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (Z_to_bv 64 0x15a54) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1593c) fc None m (seg_rom rsegs)).

Definition F_take_kd_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (i li SP KD KN AD AN : Z) (jk : list byte),
  s10 = Z_to_bv 64 li -> s8 = Z_to_bv 64 i -> s5 = Z_to_bv 64 (B + 4) -> s1 = Z_to_bv 64 KD ->
  sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= i -> 4 <= li -> i + li <= Z.of_nat (length ck) ->
  KD <> 0 -> 1 <= KN -> rw_cells rsegs m KD [CB (Z.to_nat KN) jk] ->
  apart KD KN B (Z.of_nat (length ck)) -> apart KD KN (SP + -144) 144 ->
  mem_inv rsegs m ->
  (forall m',
     munch [(KD, KD + KN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     cstr_at m' KD (cut_text (slice ck (i + RTA_HDR) (li - RTA_HDR)) KN) ->
     (exists j, rw_cells rsegs m' KD [CB (Z.to_nat KN) j]) ->
     forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (Z_to_bv 64 0x15a40) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159e4) fc None m (seg_rom rsegs)).

(* ==========================================================================
   F_kind, 0x159ac: the loop over the attributes inside one IFLA_LINKINFO (s8 = i, s3 = il,
   il >= 4). `acc` is what the attributes before it put in the buffers. Leaves by 0x15a54.
   ========================================================================== *)
Definition F_kind_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (fu : nat) (i il SP KD KN AD AN : Z) (acc : attrs),
  s6 = Z_to_bv 64 B -> s5 = Z_to_bv 64 (B + 4) -> s8 = Z_to_bv 64 i -> s3 = Z_to_bv 64 il ->
  a4 = Z_to_bv 64 4 -> a5 = Z_to_bv 64 1 -> a6 = Z_to_bv 64 3 -> s9 = Z_to_bv 64 0x1fffc ->
  s1 = Z_to_bv 64 KD -> sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= i -> i + il <= Z.of_nat (length ck) -> 4 <= il < Z.of_nat fu ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m acc KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m ->
  (forall m',
     let acc' := Attrs (kind_scan fu ck i il (a_kind acc)) (a_alias acc) in
     munch [(KD, KD + bw KD KN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' acc' KD KN AD AN ->
     (a_kind acc' = None -> munch [] m m') ->
     forall ra' t0' t1' t2' a0' a1' a2' a3' a7' s2' s3' s8' s10' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1)
                (Z_to_bv 64 3) a7' s2' s3' s4 s5 s6 s7 s8' s9 s10' s11 t3' t4' t5' t6')
           F (Z_to_bv 64 0x15a54) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x159ac) fc None m (seg_rom rsegs)).

(* ==========================================================================
   F_attr, 0x158f4: the attribute loop of the first RTM_NEWLINK (s11 = a, s7 = al, al >= 4).
   Leaves only by 0x1584c with a0 = 0.
   ========================================================================== *)
Definition F_attr_spec : Prop :=
  forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (B : Z) (ck : list byte) (fu : nat) (a al SP KD KN AD AN : Z) (acc : attrs),
  s6 = Z_to_bv 64 B -> s5 = Z_to_bv 64 (B + 4) -> s11 = Z_to_bv 64 a -> s7 = Z_to_bv 64 al ->
  a4 = Z_to_bv 64 4 -> a5 = Z_to_bv 64 1 -> a6 = Z_to_bv 64 3 -> s9 = Z_to_bv 64 0x1fffc ->
  s1 = Z_to_bv 64 KD -> s0 = Z_to_bv 64 AD -> sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) (spill_cells AN B KN AD KD) ->
  bytes_at rsegs m B ck -> (length ck <= 4096)%nat -> 0 <= B -> B + 4096 <= 2 ^ 63 ->
  0 <= a -> a + al <= Z.of_nat (length ck) -> 4 <= al < Z.of_nat fu ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  bufs m acc KD KN AD AN -> bufsep B (Z.of_nat (length ck)) SP KD KN AD AN ->
  mem_inv rsegs m ->
  (forall m',
     let accF := attr_scan fu ck a al acc in
     munch [(KD, KD + bw KD KN); (AD, AD + bw AD AN)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     bufs m' accF KD KN AD AN ->
     (a_kind accF = None -> munch [(AD, AD + bw AD AN)] m m') ->
     (a_alias accF = None -> munch [(KD, KD + bw KD KN)] m m') ->
     forall ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s7' s8' s10' s11' t3' t4' t5' t6',
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                s2' s3' s4' s5 s6 s7' s8' s9 s10' s11' t3' t4' t5' t6')
           F (Z_to_bv 64 0x1584c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158f4) fc None m (seg_rom rsegs)).
