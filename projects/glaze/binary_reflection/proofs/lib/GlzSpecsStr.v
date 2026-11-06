(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module DrvNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Module DN.
(* [comment removed for export] *)
Definition P_STDIO_WRITE : Z := 0x649a0.

Definition P_EXIT : Z := 0x617e0.
   (* [comment removed for export] *)
Definition P_EXIT_ECALL : Z := 0x61550.
Definition FILE1 : Z := 0x75858.          (* [comment removed for export] *)
Definition FILE2 : Z := 0x75768.          (* [comment removed for export] *)
Definition SBUF : Z := 0xa6bf8.           (* [comment removed for export] *)
Definition SBUF_SZ : Z := 1024.
Definition TPV : Z := 0x86520.            (* [comment removed for export] *)
Definition TID_CELL : Z := 0x86478.       (* [comment removed for export] *)
Definition CANARY : Z := 0xa6790.         (* [comment removed for export] *)
Definition GOT_CANARY : Z := 0x746f0.
Definition FR_SW : Z := 112.              (* [comment removed for export] *)
Definition FR_EXIT : Z := 128.            (* [comment removed for export] *)
Definition UP_EXIT : Z := 16.             (* [comment removed for export] *)
Definition SPLO : Z := 2 ^ 32 + 144.      (* [comment removed for export] *)
Definition SPHI : Z := 2 ^ 47.
Definition RW_MAX : Z := 2 ^ 17.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_cells : list (Z * nat * Z) :=
  [(0xa67b3, 1%nat, 0); (0xa6be0, 8%nat, 0); (0xa6bd0, 8%nat, 0);                  (* [comment removed for export] *)
   (0x75940, 8%nat, FILE1); (0x75850, 8%nat, FILE2);                              (* [comment removed for export] *)
   (FILE2 + 140, 4%nat, 2 ^ 32 - 1)].                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Section Nodes.
Variable segs : list Segment.
Variable nx0 : nat.

Definition reg_is (cs : acs) (r : nat) (v : Z) : bool :=
  match reg_lit cs r with Some x => Z.eqb x v | None => false end.
Definition at_sys (cs : acs) (a7 : Z) : bool := (is_ecall_at segs cs && reg_is cs 17 a7)%bool.


(* [comment removed for export] *)
Definition cells_ok (k : list kentry) (cells : list (Z * nat * Z)) : bool :=
  forallb (fun c => match c with (a, w, v) =>
             match kreadZ segs k (ELit 0) a w with Some x => Z.eqb x (v mod two64) | None => false end end) cells.

(* [comment removed for export] *)
Definition kbytes (n : nat) (k : list kentry) (b : expr) (o : Z) : option (list Z) := kread_bytes segs n k b o.

(* [comment removed for export] *)
Definition range_pieces (k : list kentry) (p n : expr) : option (list spiece) :=
  let '(b, o) := split_lit p in
  match lit_of n with
  | Some 0 => Some []
  | Some m => if Z.ltb 4096 m then None else
              match kbytes (Z.to_nat m) k b o with Some bs => Some [SPLit bs] | None => None end
  | None => match List.find (fun K => match K with KBlob (SA kb ko) kl _ => expr_eqb kb b && Z.eqb ko o && expr_eqb kl n | _ => false end) k with
            | Some (KBlob _ _ j) => Some [SPBlob j]
            | _ => None
            end
  end.

(* [comment removed for export] *)
Definition sp_ok (cs : acs) (fr : Z) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  match xlo k sp, xhi k sp with
  | Some lo, Some hi => (Z.leb (SPLO + fr) lo && Z.leb hi SPHI && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - fr) (ELit fr))%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition sp_ok_up (cs : acs) (fr up : Z) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  match xlo k sp, xhi k sp with
  | Some lo, Some hi => (Z.leb (SPLO + fr) lo && Z.leb (hi + up) SPHI && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - fr) (ELit (fr + up)))%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition frame_ok (cs : acs) (fr : Z) : bool :=
  let '(spb, spk) := split_lit (reg cs 2) in in_floor (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - fr) (ELit fr).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssp_ok (k : list kentry) : bool :=
  match kreadZ segs k (ELit 0) GOT_CANARY 8, kread8e segs k (ELit 0) CANARY with
  | Some g, Some _ => Z.eqb g CANARY
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition node_ioctl (cs : acs) : option acs :=
  if (at_sys cs 29 && (reg_is cs 10 1 || reg_is cs 10 2) && reg_is cs 11 0x5413)%bool
  then Some (set_pc (set_reg cs 10 (ELit (two64 - 25))) (pc cs + 4)) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_lits (k : list kentry) (f : Z) : option (Z * Z * Z * Z * Z) :=
  match kreadZ segs k (ELit 0) (f + 120) 4, kreadZ segs k (ELit 0) (f + 88) 8, kreadZ segs k (ELit 0) (f + 96) 8,
        kreadZ segs k (ELit 0) (f + 56) 8, kreadZ segs k (ELit 0) (f + 40) 8 with
  | Some fd, Some buf, Some bsz, Some wb, Some wp => Some (fd, buf, bsz, wb, wp)
  | _, _, _, _, _ => None
  end.

Definition node_stdio_write (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_STDIO_WRITE) then None else
  let k := kn cs in
  match reg_lit cs 10, ret_lit cs with
  | Some f, Some ret =>
      if negb ((Z.eqb f FILE1 || Z.eqb f FILE2) && sp_ok cs FR_SW && frame_ok cs FR_SW && ssp_ok k && fresh_ok nx0 cs
               && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then None else
      match file_lits k f with
      | Some (fd, buf, bsz, wb, wp) =>
          if negb (((Z.eqb fd 1 && Z.eqb f FILE1) || (Z.eqb fd 2 && Z.eqb f FILE2))                   (* [comment removed for export] *)
                   && Z.leb wb wp && Z.leb (wp - wb) 2048
                   && ((Z.eqb wb 0 && Z.eqb wp 0) || (Z.leb 0x75000 wb && Z.leb wp 0xa7000))       (* [comment removed for export] *)
                   && Z.leb 0x75000 buf && Z.leb (buf + bsz) 0xa7000 && Z.leb 0 bsz)%bool then None else
          let s := reg cs 11 in let l := reg cs 12 in
          let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
          (* [comment removed for export] *)
          let lok := match xhi k l, xhi k s with
                     | Some lh, Some sh => (Z.leb (wp - wb + lh) RW_MAX && Z.leb (sh + lh) SPHI)%bool
                     | _, _ => false end in
          let sdisj := (bflat_x k sb sk l && disj_x k sb sk l spb (spk - FR_SW) (ELit FR_SW))%bool in
          if negb (lok && sdisj)%bool then None else
          match kbytes (Z.to_nat (wp - wb)) k (ELit 0) wb, range_pieces k s l with
          | Some pend, Some ext =>
              let k1 := kn_havoc k spb (spk - FR_SW) (ELit FR_SW) in
              let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 32) in
              let k3 := [KWord (SA (ELit 0) (f + 32)) 8 (ELit (buf + bsz)); KWord (SA (ELit 0) (f + 40)) 8 (ELit buf);
                         KWord (SA (ELit 0) (f + 56)) 8 (ELit buf)] ++ k2 in
              match after_call nx0 cs ret (Some l) k3 with
              | Some cs' => Some (fd, (match pend with [] => [] | _ => [SPLit pend] end) ++ ext, cs')
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_covers (k : list kentry) (a n : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => (Z.leb lo a && Z.leb (a + n) hi)%bool | _ => false end) k.

Definition stdout_pending (k : list kentry) : option (list Z) :=
  if kimg_covers k FILE1 232 then Some [] else
  match kreadZ segs k (ELit 0) (FILE1 + 140) 4, kreadZ segs k (ELit 0) (FILE1 + 72) 8, kreadZ segs k (ELit 0) (FILE1 + 120) 4,
        kreadZ segs k (ELit 0) (FILE1 + 88) 8, kreadZ segs k (ELit 0) (FILE1 + 96) 8 with
  | Some lock, Some wr, Some fd, Some buf, Some bsz =>
      if negb (Z.eqb lock (2 ^ 32 - 1) && Z.eqb wr P_STDIO_WRITE && Z.eqb fd 1 && Z.eqb buf SBUF && Z.eqb bsz SBUF_SZ)%bool then None else
      match kreadZ segs k (ELit 0) (FILE1 + 56) 8, kreadZ segs k (ELit 0) (FILE1 + 40) 8,
            kreadZ segs k (ELit 0) (FILE1 + 8) 8, kreadZ segs k (ELit 0) (FILE1 + 16) 8 with
      | Some wb, Some wp, Some rp, Some re =>
          if negb (Z.eqb rp re && Z.leb 0xa6798 wb && Z.leb wb wp && Z.leb wp 0xa7000 && Z.leb (wp - wb) RW_MAX)%bool then None else
          if Z.eqb wb wp then Some [] else if ssp_ok k then kbytes (Z.to_nat (wp - wb)) k (ELit 0) wb else None
      | _, _, _, _ => None
      end
  | _, _, _, _, _ => None
  end.

Definition exit_succ (cs : acs) : acs := set_pc (set_reg (set_reg cs 10 (reg cs 8)) 17 (ELit 94)) P_EXIT_ECALL.   (* [comment removed for export] *)

Definition node_exit (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_EXIT) then None else
  let k := kn cs in
  match reg_lit cs 8, reg_lit cs 4 with                                  (* [comment removed for export] *)
  | Some _, Some tp =>
      if negb (Z.eqb tp TPV && sp_ok_up cs FR_EXIT UP_EXIT && cells_ok k exit_cells && Nat.eqb (length (s_regs (a_ss cs))) 32
              )%bool then None else
      (* [comment removed for export] *)
      match kread8e segs k (ELit 0) (FILE2 + 40), kread8e segs k (ELit 0) (FILE2 + 56),
            kread8e segs k (ELit 0) (FILE2 + 8), kread8e segs k (ELit 0) (FILE2 + 16) with
      | Some w2, Some b2, Some r2, Some e2 =>
          if negb (expr_eqb w2 b2 && expr_eqb r2 e2)%bool then None else
          match stdout_pending k with
          | Some bs => Some (1, (match bs with [] => [] | _ => [SPLit bs] end), exit_succ cs)
          | None => None
          end
      | _, _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition XNd (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with 63%nat => node_ioctl cs | _ => None end.
Definition XEd (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 64%nat => node_stdio_write cs
  | 65%nat => node_exit cs
  | _ => None
  end.
End Nodes.
End DN.
End DrvNodes.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzContracts.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.GlzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

Section Contracts.
(* [comment removed for export] *)
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable IT : itab.
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).   (* [comment removed for export] *)
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
Variable bcap ccap : Z.          (* [comment removed for export] *)

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition OBL_imgload : Prop := node1_stmt always (node_imgload IT nx0 G).
Definition OBL_opnew : Prop := GPS.node1_stmtN SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ always (node_opnew nx0 G bcap ccap).   (* [comment removed for export] *)
Definition OBL_free : Prop := node1_stmt always (node_free nx0 G).
Definition OBL_blkfact : Prop := forall args, node1_stmt always (node_blkfact G args).   (* [comment removed for export] *)
Definition OBL_opdel : Prop := node1_stmt always (node_opdel nx0 G).
Definition OBL_opdel_sized : Prop := node1_stmt always (node_opdel_sized nx0 G).
Definition OBL_memcpy : Prop := node1_stmt always (node_memcpy SEGS A nx0 G).
Definition OBL_memset : Prop := node1_stmt always (node_memset A nx0 G).
Definition OBL_memmove : Prop := node1_stmt always (node_memmove SEGS A nx0 G).
Definition OBL_strlen : Prop := node1_stmt always (node_strlen nx0 G).

(* [comment removed for export] *)
Definition node2_stmt (node : acs -> option (acs * acs)) : Prop :=
  forall cs csa csb E fx R M model T,
    GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model -> node cs = Some (csa, csb) -> T [] ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E' csa fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF SEGS fx' R' (pc csa) M' model') T) ->
    (forall E' fx' R' M' model',
        env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E' csb fx' R' M' model' ->
        m_fs model' = m_fs model -> RZ (cfgF SEGS fx' R' (pc csb) M' model') T) ->
    RZ (cfgF SEGS fx R (pc cs) M model) T.
Definition OBL_str_resize2 : Prop := forall args, node2_stmt (node_str_resize2 SEGS nx0 G bcap ccap args).



(* [comment removed for export] *)
Record gcontracts : Prop := GC {
  gc_imgload : OBL_imgload;
  gc_opnew : OBL_opnew;
  gc_free : OBL_free;       gc_blkfact : OBL_blkfact;   gc_opdel : OBL_opdel;     gc_opdel_sized : OBL_opdel_sized;
  gc_memcpy : OBL_memcpy;   gc_memset : OBL_memset;   gc_memmove : OBL_memmove;   gc_strlen : OBL_strlen
}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma XNg_sound : gcontracts -> GPS.ext_stmt SEGS nx0 (XNg SEGS IT A nx0 G bcap ccap) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof.
  intros GCs id args. unfold XNg.
  destruct GCs as [g0 g20 g11 g13 g21 g22 g1 g2 g3 g4].
  repeat (destruct id as [|id];
    [ first [ assumption | apply GPS.node1_stmt_N; assumption
            | apply GPS.node1_stmt_N; exact (g13 args)
            | apply GPS.node1_stmt_N; exact (node_divmagic_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ args)
            | apply GPS.node1_stmt_N; exact (node_enumrange_sound SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ args)
            | (intros cs cs' E fx R M model T _ _ _ Hn; discriminate Hn) ] |]).
  intros cs cs' E fx R M model T _ _ _ Hn. discriminate Hn.
Qed.


(* [comment removed for export] *)
Lemma XBg_sound : OBL_str_resize2 -> GPS.ext2_stmt SEGS nx0 (XBg SEGS nx0 G bcap ccap) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof.
  intros OB id args. unfold XBg.
  repeat (destruct id as [|id]; [first [exact (OB args) | (intros cs csa csb E fx R M model T _ Hn; discriminate Hn)] |]).
  intros cs csa csb E fx R M model T _ Hn. discriminate Hn.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition blk_ok (p n : Z) : Prop :=
  PTRLO <= p /\ p + n <= CEIL_run /\ (p + n <= g_img_lo G \/ g_img_hi G <= p).

(* [comment removed for export] *)
Definition alloc_changed (stk : Z) (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
  (bv_unsigned a < CEIL_run /\ ~ (g_img_lo G <= bv_unsigned a < g_img_hi G) /\ ~ in_blocks Lc (bv_unsigned a))
  \/ (sp - stk <= bv_unsigned a < sp)
  \/ in_wins (g_priv G) (bv_unsigned a).

Definition callee_saved_regs : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Definition alloc_pre (stk bc cc : Z) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model)
           (Lc : list (Z * Z)) (B C ret n sp : Z) : Prop :=
  m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\ FXOK fx /\
  AINV Lc B C M mdl /\
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
  bv_unsigned (getr R (Z_to_bv 5 10)) = n /\ 1 <= n <= NMAX /\
  bv_unsigned (getr R (Z_to_bv 5 2)) = sp /\ sp mod 16 = 0 /\ CEIL_run + stk <= sp /\
  getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) /\
  (forall a : word, sp - stk <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M a 1 = true) /\
  B + mcost n <= bc /\ C + MCNT <= cc.

(* [comment removed for export] *)
Definition alloc_post_ok (stk : Z) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model)
           (Lc : list (Z * Z)) (B C n sp : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) (p : word) : Prop :=
  FXOK fx' /\
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) /\
  getr R' (Z_to_bv 5 10) = p /\
  bv_unsigned p mod 16 = 0 /\ blk_ok (bv_unsigned p) n /\
  (forall b m, In (b, m) Lc -> bv_unsigned p + n <= b \/ b + m <= bv_unsigned p) /\
  (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) /\
  (forall a : word, M' a <> M a -> alloc_changed stk Lc sp a) /\
  (forall a : word, sp - stk <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M' a 1 = true) /\
  AINV ((bv_unsigned p, n) :: Lc) (B + mcost n) (C + MCNT) M' mdl' /\
  m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\ m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

(* [comment removed for export] *)
Definition alloc_post_null (stk : Z) (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model)
           (Lc : list (Z * Z)) (B C sp : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) : Prop :=
  FXOK fx' /\
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) /\
  getr R' (Z_to_bv 5 10) = Z_to_bv 64 0 /\
  (forall a : word, M' a <> M a -> alloc_changed stk Lc sp a) /\
  (forall a : word, sp - stk <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M' a 1 = true) /\
  AINV Lc B C M' mdl' /\
  m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\ m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

(* [comment removed for export] *)
Definition malloc_mspecR (stk bc cc : Z) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret n sp : Z) T,
    alloc_pre stk bc cc fx R M mdl Lc B C ret n sp -> T [] ->
    (forall fx' R' M' mdl' (p : word), alloc_post_ok stk fx R M mdl Lc B C n sp fx' R' M' mdl' p ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    (forall fx' R' M' mdl', alloc_post_null stk fx R M mdl Lc B C sp fx' R' M' mdl' ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition malloc_mspec1 (FRESH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop)
           (stk bc cc : Z) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret n sp : Z) Tok,
    alloc_pre stk bc cc fx R M mdl Lc B C ret n sp -> FRESH Lc B C M mdl n -> Tok [] ->
    (forall fx' R' M' mdl' (p : word), alloc_post_ok stk fx R M mdl Lc B C n sp fx' R' M' mdl' p ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') Tok) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) Tok.
Definition alloc1_mspecR (stk bc cc : Z) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret n sp : Z) T,
    alloc_pre stk bc cc fx R M mdl Lc B C ret n sp -> T [] ->
    (forall fx' R' M' mdl' (p : word), alloc_post_ok stk fx R M mdl Lc B C n sp fx' R' M' mdl' p ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.
Definition opnew_mspecR : Z -> Z -> Z -> Z -> Prop := alloc1_mspecR.

(* [comment removed for export] *)
Definition MSTK_MALLOC : Z := 1280.



(* [comment removed for export] *)
Definition free_mspecR (stk : Z) (entry : Z) : Prop :=
  forall fx R M mdl Lc Lc' B C B' C' (ret sp : Z) (p : word) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV Lc B C M mdl ->
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = p ->
    ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C)
     \/ exists m L1 L2, Lc = L1 ++ (bv_unsigned p, m) :: L2 /\ Lc' = L1 ++ L2
                         /\ B' = Z.max 0 (B - mcost m) /\ C' = Z.max 0 (C - MCNT)) ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + stk <= sp ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - stk <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M a 1 = true) ->
    (forall fx' R' M' mdl',
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        (forall a : word, M' a <> M a -> alloc_changed stk Lc' sp a) ->
        (forall a : word, sp - stk <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        AINV Lc' B' C' M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frame_kept (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
  (owned SWIN PERMc SPTOPc Lc a /\ ~ (sp - MSTK <= bv_unsigned a < sp))
  \/ (g_ro_lo G <= bv_unsigned a < g_img_hi G /\ ~ in_wins (g_priv G) (bv_unsigned a))
  \/ (SPTOPc <= bv_unsigned a /\ sp <= SPTOPc).

(* [comment removed for export] *)
Definition nalloc_post_ok (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model)
           (Lc : list (Z * Z)) (B C n sp : Z)
           (fx' : FX) (R' : bvmap 5 word) (M' : word -> option byte) (mdl' : Model) (p : word) : Prop :=
  FXOK fx' /\
  (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) /\
  getr R' (Z_to_bv 5 10) = p /\
  bv_unsigned p mod 16 = 0 /\ blk_ok (bv_unsigned p) n /\
  (forall b m, In (b, m) Lc -> bv_unsigned p + n <= b \/ b + m <= bv_unsigned p) /\
  (forall lo hi, In (lo, hi) PERMc -> lo < hi -> bv_unsigned p + n <= lo \/ hi <= bv_unsigned p) /\
  (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + n -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) /\
  (forall a : word, frame_kept Lc sp a -> M' a = M a) /\
  (forall a : word, sp - MSTK <= bv_unsigned a < sp -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) /\
  AINV ((bv_unsigned p, n) :: Lc) (B + mcost n) (C + MCNT) M' mdl' /\
  m_halted mdl' = None /\ m_vm_lazy mdl' = [] /\ m_vm_materialized mdl' = [] /\ m_fs mdl' = m_fs mdl /\ m_fds mdl' = m_fds mdl.

Definition nalloc_pre (fx : FX) (R : bvmap 5 word) (M : word -> option byte) (mdl : Model)
           (Lc : list (Z * Z)) (B C ret n sp : Z) : Prop :=
  m_halted mdl = None /\ m_vm_lazy mdl = [] /\ m_vm_materialized mdl = [] /\ FXOK fx /\
  AINV Lc B C M mdl /\
  getr R (Z_to_bv 5 1) = Z_to_bv 64 ret /\ 0 <= ret < 2 ^ 64 /\ ret mod 2 = 0 /\
  bv_unsigned (getr R (Z_to_bv 5 10)) = n /\ 1 <= n <= NMAX /\
  bv_unsigned (getr R (Z_to_bv 5 2)) = sp /\ sp mod 16 = 0 /\ CEIL_run + MSTK <= sp /\ sp <= SPTOPc /\
  getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) /\
  (forall a : word, sp - MSTK <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M a 1 = true) /\
  B + mcost n <= bcap /\ C + MCNT <= ccap.



(* [comment removed for export] *)
Definition alloc1_nspec (XTRA : (word -> option byte) -> Prop) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret n sp : Z) T,
    nalloc_pre fx R M mdl Lc B C ret n sp -> T [] -> XTRA M ->
    (forall fx' R' M' mdl' (p : word), nalloc_post_ok fx R M mdl Lc B C n sp fx' R' M' mdl' p ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.
(* [comment removed for export] *)
Definition opnew_nspec : Z -> Prop := alloc1_nspec (fun _ => True).

(* [comment removed for export] *)
Definition malloc_nspec1 (FRESH : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Z -> Prop) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret n sp : Z) Tok,
    nalloc_pre fx R M mdl Lc B C ret n sp -> FRESH Lc B C M mdl n -> Tok [] ->
    (forall fx' R' M' mdl' (p : word), nalloc_post_ok fx R M mdl Lc B C n sp fx' R' M' mdl' p ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') Tok) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) Tok.

Definition free_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc Lc' B C B' C' (ret sp : Z) (p : word) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV Lc B C M mdl ->
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = p ->
    ((p = Z_to_bv 64 0 /\ Lc' = Lc /\ B' = B /\ C' = C)
     \/ exists m L1 L2, Lc = L1 ++ (bv_unsigned p, m) :: L2 /\ Lc' = L1 ++ L2
                         /\ Z.max 0 (B - mcost m) <= B' /\ Z.max 0 (C - MCNT) <= C') ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + MSTK <= sp -> sp <= SPTOPc ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - MSTK <= bv_unsigned a < sp -> RiscvSemantics.store_ok SEGS M a 1 = true) ->
    (forall fx' R' M' mdl',
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        (forall a : word, frame_kept Lc' sp a -> M' a = M a) ->
        (forall a : word, sp - MSTK <= bv_unsigned a < sp -> M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
        AINV Lc' B' C' M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.

End Contracts.
End GlzContracts.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzKnowLib.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

Section KnowLib.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable G : gtable.

#[local] Notation owned := (GPS.owned SWIN PERMc SPTOPc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_kfoot (E : env) (K : kentry) (x : Z) : Prop :=
  match kfoot E K with Some (s, l) => s <= x < s + l | None => False end.

Lemma kentry_ok_footprint : forall E M M' K,
  kentry_ok SEGS E M K ->
  (forall x : word, in_kfoot E K (bv_unsigned x) -> M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K HK Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> M' x = M x) ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hd. lia. }
  unfold in_kfoot, kfoot in Hout.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn]; cbn [kentry_ok] in *;
    try exact HK.
  7: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
       rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
       rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia |].
    intros x Hx. apply Hout. rewrite (flat_u E _ _ Hfl) in Hx. lia.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_add_off : forall (x : word) (off : Z),
  0 <= bv_unsigned x + off < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (Z_to_bv 64 off))) = bv_unsigned x + off.
Proof.
  intros x off H. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

Lemma in_blocks_den : forall E live b n z,
  In (b, n) live -> GPS.uE E b <= z < GPS.uE E b + GPS.uE E n -> in_blocks (blocks_den E live) z.
Proof.
  intros E live b n z Hin Hz. exists (GPS.uE E b), (GPS.uE E n). split; [|exact Hz].
  unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

Lemma bflat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> bflat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ estart E (SA b off) < 2 ^ 64.
Proof.
  intros E M k b off n HK H. unfold bflat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. unfold two64 in H2, H3.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned3 (Lc : list (Z * Z)) (a : word) : Prop :=
  in_blocks Lc (bv_unsigned a) \/ in_wins PERMc (bv_unsigned a) \/ (CEIL_run <= bv_unsigned a < SPTOPc).
Lemma owned3_owned : forall Lc a, owned3 Lc a -> owned Lc a.
Proof. intros Lc a [H|[H|H]]; [left; exact H | right; left; exact H | right; right; left; exact H]. Qed.

(* [comment removed for export] *)
Definition sp_lin (E : env) (sp : expr) : Z := let '(spb, spk) := split_lit sp in GPS.uE E spb + spk.

Lemma owned_x_sound3 : forall E M k live perm fl top bud b off n (a : word),
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> GPS.floor_sem E fl top bud ->
  owned_x k (live ++ perm) fl top bud b off n = true ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  owned3 (blocks_den E live) a.
Proof.
  intros E M k live perm fl top bud b off n a HK Hflat Hperm Htop Hfl Ho Ha. unfold owned3. unfold owned_x in Ho. apply orb_prop in Ho as [Ho|Ho].
  - apply existsb_exists in Ho as [[lb0 ln] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct (split_lit lb0) as [lb lk] eqn:Hsp0.
    pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl0. cbn [fst snd] in Hfl0. rewrite Hsp0 in Hfl0.
    pose proof (bflat_x_sound E _ k lb lk ln HK Hfl0) as (F1 & F2 & F3).
    pose proof (xinside_sound SEGS E M k b off n lb lk ln HK Hx) as [X1 X2].
    pose proof (split_lit_denot E lb0 lb lk Hsp0) as Hd.
    rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite !estart_SA in Ha. rewrite !estart_SA in F1. rewrite !estart_SA in F2.
    unfold elenZ in *.
    pose proof (u64_range (edenot E lb)). pose proof (u64_range a). pose proof (u64_range (edenot E ln)).
    assert (Hu : GPS.uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold GPS.uE; rewrite Hd; apply u64_lit; lia).
    apply in_app_iff in Hin as [Hin|Hin].
    + left. eapply (in_blocks_den E live lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
    + right. left. rewrite <- Hperm. eapply (GPS.in_wins_den E perm lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
  - (* [comment removed for export] *)
    right. right. rewrite <- Htop. exact (proj1 (GPS.in_floor_sound SEGS E M k fl top bud b off n a HK Ho Hfl Ha)).
Qed.

Lemma owned_x_sound : forall E M k live perm fl top bud b off n (a : word),
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> GPS.floor_sem E fl top bud ->
  owned_x k (live ++ perm) fl top bud b off n = true ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  owned (blocks_den E live) a.
Proof. intros. apply owned3_owned. eapply owned_x_sound3; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lit_disjoint_sound : forall lo hi ps z,
  lit_disjoint lo hi ps = true -> lo <= z < hi -> ~ in_wins ps z.
Proof.
  intros lo hi ps z. induction ps as [|[a b] r IH]; intros H Hz [l [h [Hin Hlh]]].
  - destruct Hin.
  - cbn [lit_disjoint] in H. apply andb_prop in H as [H1 H2].
    destruct Hin as [Heq|Hin].
    + injection Heq as <- <-. apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
    + apply (IH H2 Hz). exists l, h. split; assumption.
Qed.

(* [comment removed for export] *)
Definition frame_kept (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
  (owned Lc a /\ ~ (sp - MSTK <= bv_unsigned a < sp))
  \/ (g_ro_lo G <= bv_unsigned a < g_img_hi G /\ ~ in_wins (g_priv G) (bv_unsigned a))
  \/ (SPTOPc <= bv_unsigned a /\ sp <= SPTOPc).

Lemma kn_vars_lt_filter_vars : forall v (f : kentry -> bool) l,
  kn_vars_lt v (List.filter (fun K => kentry_vars_lt v K && f K)%bool l) = true.
Proof.
  intros v f l. induction l as [|K r IH]; [reflexivity|].
  cbn [List.filter]. destruct (kentry_vars_lt v K && f K)%bool eqn:Hc; [|exact IH].
  cbn [kn_vars_lt]. apply andb_prop in Hc as [-> _]. exact IH.
Qed.

Lemma kn_vars_lt_app2 : forall v l1 l2, kn_vars_lt v l1 = true -> kn_vars_lt v l2 = true -> kn_vars_lt v (l1 ++ l2) = true.
Proof.
  intros v l1 l2 H1 H2. induction l1 as [|K r IH]; [exact H2|]. cbn [kn_vars_lt app] in *.
  apply andb_prop in H1 as [-> Hr]. exact (IH Hr).
Qed.

Lemma keep_owned_vars : forall k live fl top bud sp v, kn_vars_lt v (keep_owned G k live fl top bud sp v) = true.
Proof.
  intros k live fl top bud sp v. rewrite keep_owned_eq. unfold keep_owned_ref. destruct (split_lit sp) as [spb spk].
  apply kn_vars_lt_app2; apply kn_vars_lt_filter_vars.
Qed.

(* [comment removed for export] *)
Lemma kwr_bytes : forall E M b o n,
  kentry_ok SEGS E M (KWr (SA b o) n) <->
  (flat E (SA b o) (elenZ E n) /\ forall x : word, estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n ->
                                     RiscvSemantics.store_ok SEGS M x 1 = true).
Proof.
  intros E M b o n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl; pose proof Hfl as (F1 & F2 & F3 & F4).
  - intros x Hx. replace x with (Z_to_bv 64 (estart E (SA b o) + (bv_unsigned x - estart E (SA b o)))).
    2:{ apply bv_eq. rewrite u64_lit by lia. lia. }
    apply (H (bv_unsigned x - estart E (SA b o)) 1%nat); [lia | cbn; lia].
  - intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    eapply (store_ok_all SEGS M 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | apply H; lia | change (Z.of_nat 1) with 1; lia].
Qed.

Lemma store_ok1_ext : forall M M' (x : word), M' x = M x -> RiscvSemantics.store_ok SEGS M' x 1 = RiscvSemantics.store_ok SEGS M x 1.
Proof. intros M M' x H. cbn [RiscvSemantics.store_ok]. unfold wview. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma above_x_sound : forall E M k top sp b off n (x : word),
  know_ok SEGS E M k -> above_x k top sp b off n = true -> sptop_den E top = SPTOPc ->
  estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
  SPTOPc <= bv_unsigned x /\ bv_unsigned (edenot E sp) <= SPTOPc.
Proof.
  intros E M k top sp b off n x HK H Htop Hx. unfold above_x in H.
  destruct (xlo k top) as [tlo|] eqn:Ht; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H.
  pose proof (xlo_sound SEGS E M k top tlo HK Ht) as T0.
  pose proof (lin_ge0_sound SEGS E M k [(b, off)] [(top, 0)] HK X1) as L1. cbn [xt_den] in L1.
  pose proof (lin_ge0_sound SEGS E M k [(top, 0)] [(sp, 0)] HK X0) as L2. cbn [xt_den] in L2.
  assert (HT : SPTOPc = bv_unsigned (edenot E top)).
  { rewrite <- Htop. unfold sptop_den, GPS.uE. destruct (Z.eqb_spec (bv_unsigned (edenot E top)) 0); [lia | reflexivity]. }
  rewrite HT. rewrite estart_SA in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma img_lit_x_sound : forall E M k b off n (x : word),
  know_ok SEGS E M k -> img_lit_x G k b off n = true ->
  0 <= estart E (SA b off) -> estart E (SA b off) < 2 ^ 64 ->
  estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
  g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_priv G) (bv_unsigned x).
Proof.
  intros E M k b off n x HK H E1 E2 Hx. unfold img_lit_x in H.
  destruct (xlo k (eaddz b off)) as [lo|] eqn:Hl; [|discriminate]. destruct (xhi k (eaddz b off)) as [hi|] eqn:Hh; [|discriminate].
  destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hdj]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (xlo_sound SEGS E M k _ lo HK Hl) as S1. pose proof (xhi_sound SEGS E M k _ hi HK Hh) as S2. pose proof (xhi_sound SEGS E M k n nh HK Hnh) as S3.
  unfold eaddz in S1, S2. rewrite mkAlu_denot in S1, S2. cbn [edenot] in S1, S2. rewrite alu_add in S1, S2. unfold v_add in S1, S2.
  rewrite estart_SA in Hx, E1, E2. rewrite u_add_off in S1, S2 by lia. unfold elenZ in Hx.
  split; [lia|]. eapply lit_disjoint_sound; [exact Hdj | lia].
Qed.

Lemma keep_owned_sound : forall E M M' k live perm fl top bud sp spb spk v K,
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc ->
  split_lit sp = (spb, spk) -> 0 <= bv_unsigned (edenot E spb) + spk < 2 ^ 64 ->
  GPS.floor_sem E fl top bud ->                                                       (* [comment removed for export] *)
  (forall a : word, frame_kept (blocks_den E live) (bv_unsigned (edenot E sp)) a -> M' a = M a) ->
  (forall a : word, bv_unsigned (edenot E sp) - MSTK <= bv_unsigned a < bv_unsigned (edenot E sp) ->
                    M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
  In K (keep_owned G k (live ++ perm) fl top bud sp v) -> kentry_ok SEGS E M' K.
Proof.
  intros E M M' k live perm fl top bud sp spb spk v K HK Hflat Hperm Htop Hsp Hspr Hceil Hfr Hscr Hin.
  rewrite keep_owned_eq in Hin. unfold keep_owned_ref in Hin. rewrite Hsp in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK. unfold keep_sticky in Hkeep.
    destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn];
      try exact HKK; try discriminate.
    + (* [comment removed for export] *) apply andb_prop in Hkeep as [Hkeep Hdj]. apply andb_prop in Hkeep as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
      eapply kentry_ok_footprint; [exact HKK|]. intros x Hx. unfold in_kfoot, kfoot in Hx.
      apply Hfr. right. left. split; [lia|]. eapply lit_disjoint_sound; [exact Hdj | lia].
    + (* [comment removed for export] *) apply (proj1 (kwr_bytes E M b o nn)) in HKK as [Hfl HS]. apply (proj2 (kwr_bytes E M' b o nn)). split; [exact Hfl|].
      intros x Hx. apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn x HK Habv Htop Hx) as AB.
          rewrite (store_ok1_ext M M' x); [apply HS; exact Hx|]. apply Hfr. right; right. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn x HK Hflat Hperm Htop Hceil Hkeep Hx) as Ho.
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp) - MSTK)) as [Hl|Hge];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp))) as [Hl2|Hge2]; [exact (proj2 (Hscr x ltac:(lia)))|]].
      all: rewrite (store_ok1_ext M M' x); [apply HS; exact Hx|]; apply Hfr; left; split; [apply owned3_owned; exact Ho | lia].
    + (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl HS]. split; [exact Hfl|]. intros i Hi.
      pose proof Hfl as (F1 & F2 & F3 & F4). set (x := Z_to_bv 64 (estart E (SA b o) + i)).
      assert (Hux : bv_unsigned x = estart E (SA b o) + i) by (unfold x; apply u64_lit; lia).
      apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn x HK Habv Htop ltac:(rewrite Hux; lia)) as AB.
          rewrite (Hfr x); [apply HS; exact Hi|]. right; right. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn x HK Hflat Hperm Htop Hceil Hkeep ltac:(rewrite Hux; lia)) as Ho.
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp) - MSTK)) as [Hl|Hge];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp))) as [Hl2|Hge2]; [exact (proj1 (Hscr x ltac:(lia)))|]].
      all: rewrite (Hfr x); [apply HS; exact Hi|]; left; split; [apply owned3_owned; exact Ho | lia].
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    assert (HKc : know_ok SEGS E M (kn_cutout k spb (spk - MSTK) (ELit MSTK))).
    { eapply know_ok_cutout; [exact HK|]. intros; reflexivity. }
    pose proof (proj1 (Forall_forall _ _) HKc K Hin) as HKK.
    unfold keep_content in Hkeep.
    destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn];
      cbn [kentry_range] in Hkeep; try discriminate.
    1: assert (Hw8 : Z.of_nat w <= 8) by (cbn [kentry_ok] in HKK; destruct HKK as [Hw _]; lia).
    all: rewrite Hsp in Hkeep.
    all: pose proof (split_lit_denot E sp spb spk Hsp) as Hspd.
    all: (eapply kentry_ok_footprint; [exact HKK|]; intros x Hx; unfold in_kfoot, kfoot in Hx).
    (* [comment removed for export] *)
    all: (apply orb_prop in Hkeep as [Hkeep|Himg];
          [| apply Hfr; right; left;
             cbn [kentry_ok] in HKK;
             lazymatch type of HKK with
             | _ /\ flat _ _ _ /\ _ => destruct HKK as (Hw8' & Hfl0 & Hrest0)
             | flat _ _ _ /\ _ => destruct HKK as [Hfl0 Hrest0]
             end;
             destruct Hfl0 as (G1 & G2 & G3 & G4);
             eapply (img_lit_x_sound E M k b o _ x HK Himg); [lia | lia |];
             rewrite ?APS.elenZ_lit by lia; exact Hx ]).
    all: (apply orb_prop in Hkeep as [Hkeep|Habv];
          [ apply andb_prop in Hkeep as [Hown Hap]; apply Hfr; left
          | apply Hfr; right; right;
            pose proof (above_x_sound E M k top sp _ _ _ x HK Habv Htop) as AB;
            rewrite !estart_SA in AB, Hx; unfold elenZ in AB, Hx; cbn [edenot] in AB, Hx;
            rewrite ?(u64_lit (Z.of_nat w)) in AB by lia; exact (AB Hx) ]).
    all: pose proof (ranges_apart_x_sound SEGS E M k _ _ _ spb (spk - MSTK) (ELit MSTK) HK Hap) as Hd.
    all: (rewrite !estart_SA in Hd; rewrite !estart_SA in Hx; unfold elenZ in Hd, Hx; cbn [edenot] in Hd, Hx;
          rewrite (u64_lit MSTK) in Hd by (unfold MSTK; lia); rewrite ?(u64_lit (Z.of_nat w)) in Hd by lia; rewrite Hspd).
    all: (pose proof (u64_range (edenot E spb)); pose proof (u64_range x)).
    all: (split; [ eapply owned_x_sound; [exact HK | exact Hflat | exact Hperm | exact Htop | exact Hceil | exact Hown |]; rewrite !estart_SA; unfold elenZ; cbn [edenot]; rewrite ?u64_lit by lia; lia |]).
    all: intros [HA HB]; rewrite u64_lit in HA, HB by lia; unfold MSTK in *; lia.
Qed.

(* [comment removed for export] *)
Definition kept_loc (Lc : list (Z * Z)) (z : Z) : Prop :=
  in_blocks Lc z \/ in_wins PERMc z \/ (CEIL_run <= z < SPTOPc) \/ SPTOPc <= z \/ (g_ro_lo G <= z < g_img_hi G).

Lemma owned3_kept_loc : forall Lc (x : word), owned3 Lc x -> kept_loc Lc (bv_unsigned x).
Proof. intros Lc x [H|[H|H]]; unfold kept_loc; tauto. Qed.

Lemma keep_owned_loc : forall E M k live perm fl top bud sp spb spk v K z,
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc ->
  split_lit sp = (spb, spk) -> GPS.floor_sem E fl top bud ->
  In K (keep_owned G k (live ++ perm) fl top bud sp v) -> in_kfoot E K z ->
  kept_loc (blocks_den E live) z.
Proof.
  intros E M k live perm fl top bud sp spb spk v K z HK Hflat Hperm Htop Hsp Hceil Hin Hz.
  rewrite keep_owned_eq in Hin. unfold keep_owned_ref in Hin. rewrite Hsp in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK. unfold keep_sticky in Hkeep. unfold in_kfoot, kfoot in Hz.
    destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn];
      try discriminate; try (exfalso; exact Hz).
    + (* [comment removed for export] *) apply andb_prop in Hkeep as [Hkeep Hdj]. apply andb_prop in Hkeep as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold kept_loc. right; right; right; right. lia.
    + (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as [(F1 & F2 & F3 & F4) _].
      apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn (Z_to_bv 64 z) HK Habv Htop ltac:(rewrite u64_lit by lia; lia)) as [AB _].
          rewrite u64_lit in AB by lia. unfold kept_loc. right; right; right; left. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn (Z_to_bv 64 z) HK Hflat Hperm Htop Hceil Hkeep ltac:(rewrite u64_lit by lia; lia)) as Ho.
      apply owned3_kept_loc in Ho. rewrite u64_lit in Ho by lia. exact Ho.
    + (* [comment removed for export] *) cbn [kentry_ok] in HKK. destruct HKK as [(F1 & F2 & F3 & F4) _].
      apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn (Z_to_bv 64 z) HK Habv Htop ltac:(rewrite u64_lit by lia; lia)) as [AB _].
          rewrite u64_lit in AB by lia. unfold kept_loc. right; right; right; left. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn (Z_to_bv 64 z) HK Hflat Hperm Htop Hceil Hkeep ltac:(rewrite u64_lit by lia; lia)) as Ho.
      apply owned3_kept_loc in Ho. rewrite u64_lit in Ho by lia. exact Ho.
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    assert (HKc : know_ok SEGS E M (kn_cutout k spb (spk - MSTK) (ELit MSTK))).
    { eapply know_ok_cutout; [exact HK|]. intros; reflexivity. }
    pose proof (proj1 (Forall_forall _ _) HKc K Hin) as HKK.
    unfold keep_content in Hkeep.
    destruct (kentry_range K) as [[[b o] len]|] eqn:HKR; [|destruct K as [[? ?] ? ?|[? ?] ?|[? ?] ? ?| | | |[? ?] ?| |[? ?] ? ?|[? ?] ?]; discriminate].
    rewrite Hsp in Hkeep.
    (* [comment removed for export] *)
    assert (FP : estart E (SA b o) <= z < estart E (SA b o) + elenZ E len /\ 0 <= estart E (SA b o) /\ estart E (SA b o) + elenZ E len <= 2 ^ 64).
    { unfold in_kfoot, kfoot in Hz.
      destruct K as [[b' o'] w vv|[b' o'] nn|[b' o'] nn kb|ilo ihi|e m|e rlo rhi|[b' o'] nn|a1 n1 a2 n2|[b' o'] nn fc|[b' o'] nn];
        cbn [kentry_range] in HKR; try discriminate; injection HKR as <- <- <-; cbn [kentry_ok] in HKK.
      (* [comment removed for export] *)
      - destruct HKK as (Hw8 & (F1 & F2 & F3 & F4) & _). unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. lia.
      - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
      - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia.
      - destruct HKK as ((F1 & F2 & F3 & F4) & _). lia. }
    destruct FP as (Hzr & E1 & E2).
    assert (Hx : estart E (SA b o) <= bv_unsigned (Z_to_bv 64 z) < estart E (SA b o) + elenZ E len) by (rewrite u64_lit by lia; lia).
    assert (KK : match K with KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ => true | _ => false end = true ->
                 ((owned_x k (live ++ perm) fl top bud b o len && ranges_apart_x k b o len spb (spk - MSTK) (ELit MSTK)) || above_x k top sp b o len || img_lit_x G k b o len)%bool = true).
    { intros HKm. destruct K; try discriminate HKm; exact Hkeep. }
    assert (HKm : match K with KWord _ _ _ | KZero _ _ | KFill _ _ _ | KBlob _ _ _ => true | _ => false end = true).
    { destruct K; try reflexivity; cbn [kentry_range] in HKR; discriminate. }
    specialize (KK HKm). clear Hkeep.
    apply orb_prop in KK as [KK|Himg].
    2:{ pose proof (img_lit_x_sound E M k b o len (Z_to_bv 64 z) HK Himg E1 ltac:(lia) Hx) as [IM _].
        rewrite u64_lit in IM by lia. unfold kept_loc. right; right; right; right. exact IM. }
    apply orb_prop in KK as [KK|Habv].
    2:{ pose proof (above_x_sound E M k top sp b o len (Z_to_bv 64 z) HK Habv Htop Hx) as [AB _].
        rewrite u64_lit in AB by lia. unfold kept_loc. right; right; right; left. exact AB. }
    apply andb_prop in KK as [Hown _].
    pose proof (owned_x_sound3 E M k live perm fl top bud b o len (Z_to_bv 64 z) HK Hflat Hperm Htop Hceil Hown Hx) as OW.
    apply owned3_kept_loc in OW. rewrite u64_lit in OW by lia. exact OW.
Qed.


(* [comment removed for export] *)
Lemma dst_owned_sound : forall E M cs (x : word),
  know_ok SEGS E M (kn cs) -> dst_owned cs = true ->
  wins_den E (a_ghost cs) = PERMc -> sptop_den E (a_brk cs) = SPTOPc -> GPS.floor_sem E (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) ->
  GPS.uE E (reg cs 10) <= bv_unsigned x < GPS.uE E (reg cs 10) + GPS.uE E (reg cs 12) ->
  owned (blocks_den E (a_vis cs)) x.
Proof.
  intros E M cs x HK H Hperm Htop Hfloor Hx. unfold dst_owned in H.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsp.
  apply andb_prop in H as [Hown Hflat]. unfold live_flat in Hflat.
  pose proof (split_lit_denot E (reg cs 10) db dk Hsp) as Hd.
  assert (Hes : 0 <= estart E (SA db dk) /\ estart E (SA db dk) + elenZ E (reg cs 12) <= 2 ^ 64).
  { unfold owned_x in Hown. apply orb_prop in Hown as [Ho|Ho].
    - apply existsb_exists in Ho as [[lb0 ln] [Hin Hxi]]. cbn [fst snd] in Hxi.
      destruct (split_lit lb0) as [lb lk] eqn:Hs2.
      pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl. cbn [fst snd] in Hfl. rewrite Hs2 in Hfl.
      pose proof (bflat_x_sound E _ (kn cs) lb lk ln HK Hfl) as (F1 & F2 & F3).
      pose proof (xinside_sound SEGS E M (kn cs) db dk (reg cs 12) lb lk ln HK Hxi) as [X1 X2].
      pose proof (u64_range (edenot E (reg cs 12))). unfold elenZ in *. lia.
    - unfold in_floor in Ho. destruct (split_lit (a_brk cs)) as [tb tk] eqn:Htsp.
      destruct (base_range (kn cs) tb) as [[tlo thi]|] eqn:Hbr; [|destruct (acs_floor (a_maps cs)); discriminate].
      pose proof (base_range_sound SEGS E M (kn cs) tb tlo thi HK Hbr) as [T1 T2].
      pose proof (u64_range (edenot E (reg cs 12))). pose proof (u64_range (edenot E tb)). pose proof (u64_range (edenot E db)).
      rewrite estart_SA. unfold elenZ.
      destruct (acs_floor (a_maps cs)) as [f|].
      + apply andb_prop in Ho as [Ho L2]. apply andb_prop in Ho as [Ho L1]. apply andb_prop in Ho as [Ho G3]. apply andb_prop in Ho as [G0 G1]. apply Z.ltb_lt in G3. apply Z.ltb_lt in G1.
        pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK L1) as X1. pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HK L2) as X2.
        cbn [xt_den] in X1, X2. pose proof (u64_range (edenot E f)). unfold GPS.uE, two64 in *. lia.
      + apply andb_prop in Ho as [Hg Hxi]. apply andb_prop in Hg as [Hg G3]. apply andb_prop in Hg as [G1 G2].
        apply Z.leb_le in G1. apply Z.leb_le in G2. apply Z.ltb_lt in G3.
        pose proof (xinside_sound SEGS E M (kn cs) db dk (reg cs 12) tb (tk - a_ylo cs) (ELit (a_ylo cs)) HK Hxi) as [X1 X2].
        rewrite !estart_SA in X1, X2. rewrite !(APS.elenZ_lit E) in X2 by (unfold CEIL, two64 in *; lia). unfold elenZ in *. unfold GPS.uE, CEIL, two64 in *. lia. }
  eapply owned_x_sound; [exact HK | exact Hflat | exact Hperm | exact Htop | exact Hfloor | exact Hown |].
  unfold GPS.uE in Hx. rewrite Hd in Hx. rewrite estart_SA in Hes. rewrite estart_SA.
  pose proof (u64_range (edenot E db)). pose proof (u64_range (edenot E (reg cs 12))). unfold elenZ in *.
  destruct (Z.eq_dec (bv_unsigned (edenot E (reg cs 12))) 0) as [Hz|Hz].
  - lia.
  - rewrite u64_lit in Hx by lia. lia.
Qed.

End KnowLib.
End GlzKnowLib.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzCallLib.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
#[local] Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing) : bool_scope.

Module GCL.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
  forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
  unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
  (forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
    cbn [edenot]. apply getr_zero.
  - apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
  unfold caller_saved.
  repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
  ~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
  rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
  destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
  List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
  intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
  inversion Hnd as [|c' t' Hnotin Hnd']; subst.
  cbn [sr_fresh]. destruct j as [|j].
  - cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
  - cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
  Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
                then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
                else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
  intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
  destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
  ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
  intros E nx R' j Hj. cbn [ext_call ev].
  replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
  2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
  f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
  intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
  cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

(* [comment removed for export] *)
Lemma regs_after_call : forall E sr R R' nx rv,
  regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
  match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
  regs_ok (ext_call E nx R')
          (match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
  intros E sr R R' nx rv HR Hsv Hkept Hrv.
  pose proof (ext_call_agree E nx R') as Hag.
  assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
  { intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
  apply regs_ok_pointwise. intros r Hr0.
  assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
  { intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
  pose proof (ridx_range r) as Hrr.
  assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
  { destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
    - destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
      rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
      cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
    - rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
      rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
      destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
      exact X. }
  destruct rv as [e|]; [|exact GEN].
  destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
  destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
  rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
  rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_same : forall bs m (a : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall j, (j < length bs)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
  wbytes m a bs = m.
Proof.
  intros bs m a Hnw Hall. apply functional_extensionality. intros x.
  pose proof (u64_range x) as Hx.
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
  2: { apply wbytes_out; [exact Hnw | lia]. }
  set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
  assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  { subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
    symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined : forall bs m (a : word) j,
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
  wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_all : forall segs m n (a : word) b,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rdn_nth : forall segs m n (a : word) bs j,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn segs m a n = Some bs -> (j < n)%nat ->
  rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
  destruct j as [|j'].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
  - cbn [nth]. destruct n as [|n'']; [lia|].
    assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
    apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
  rdn segs m a n = Some (map f (seq 0 n)).
Proof.
  intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
  cbn [rdn seq map].
  pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection H0 as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
    intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
    apply Hall. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.land (a * 2 ^ k) b = 0%Z.
Proof.
  intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k) as [Hl|Hh].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
  Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
  intros a b k Ha Hk Hb.
  rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
  Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b rest IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
  pose proof (bytes_le_to_Z_nonneg rest) as Hr.
  assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
  rewrite Hlor. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (2 ^ 8) with 256 in *. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
  (length bs <= 8)%nat ->
  word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
  assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
  { eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
  rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
  length bs = n -> (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KnowTests.
Variable segs : list Segment.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.


(* [comment removed for export] *)
Lemma kwritable_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
  cbn [kwritable_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kzero_x_sound : forall E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kzero_x allkn k b off n = true ->
  (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest].
  destruct K; try exact (IH Hrest H).
  lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
  cbn [kzero_x] in H.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
                 (forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
    replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
    apply Hz. lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n,
  know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
  lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
  destruct (Z.leb hi a ||| Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
  apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
  cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
  - destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
  exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
             /\ word_to_le_bytes w (edenot E v) = bs.

Lemma lookup_piece : forall E M k b off w v hs,
  know_ok segs E M k -> (1 <= w <= 8)%nat ->
  know_lookup segs k b off w false [] [] = LHit v [] hs ->
  flat E (SA b off) (Z.of_nat w) ->
  piece_ok E M b off w v.
Proof.
  intros E M k b off w v hs HK Hw HL Hfl.
  pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
  unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : forall E M k b off v,
  know_ok segs E M k -> kread8e segs k b off = Some v -> flat E (SA b off) 8 ->
  piece_ok E M b off 8 v.
Proof.
  intros E M k b off v HK H Hfl. unfold kread8e in H.
  destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection H as ->.
  eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : forall E M k b off z,
  know_ok segs E M k -> kreadZ segs k b off 1 = Some z -> flat E (SA b off) 1 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = Some [Z_to_bv 8 z] /\ 0 <= z < 256.
Proof.
  intros E M k b off z HK H Hfl. unfold kreadZ in H.
  destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
  destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
  pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
  destruct bs as [|b0 [|]]; try discriminate.
  cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
  pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
  rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
  split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
  rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : forall E M k len b off zs,
  know_ok segs E M k -> kread_bytes segs len k b off = Some zs ->
  0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat len <= 2 ^ 64 ->
  rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = Some (map (fun z => Z_to_bv 8 z) zs)
  /\ length zs = len /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
  intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
  - cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
  - cbn [kread_bytes] in H.
    destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
    destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
    injection H as <-.
    assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
    destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
    destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
                 ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
    split; [| split; [cbn; lia | constructor; assumption]].
    change (S len) with (1 + len)%nat. cbn [map].
    change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
    eapply rdn_app; [exact Hrd|].
    replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
    apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
    rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : forall zs, Forall (fun z => 0 <= z < 256) zs ->
  zbytes_le_to_Z zs = bytes_le_to_Z (map (fun z => Z_to_bv 8 z) zs).
Proof.
  intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
  induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma copy_facts_sound : forall E M k sb db fuel sk dk n kc,
  know_ok segs E M k ->
  copy_facts segs fuel k sb sk db dk n = Some kc -> 0 <= n -> (Z.to_nat n <= fuel)%nat ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + n <= 2 ^ 64 ->
  0 <= estart E (SA db dk) -> estart E (SA db dk) + n <= 2 ^ 64 ->
  exists bs, length bs = Z.to_nat n
    /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
    /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc.
Proof.
  intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
  - cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
    exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
  - cbn [copy_facts] in H.
    (* [comment removed for export] *)
    assert (STEP : forall (w : nat) v kr,
      (1 <= w <= 8)%nat -> Z.of_nat w <= n ->
      piece_ok E M sb sk w v ->
      copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
      kc = KWord (SA db dk) w v :: kr ->
      exists bs, length bs = Z.to_nat n
        /\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
        /\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
    { intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
      assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
      destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
                   ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
        as (bsR & HlenR & HrdR & HKR).
      exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
      - replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
        apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
        rewrite ES in HrdR.
        replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
        rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
      - intros M' HM'. constructor.
        + cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
          rewrite adenot_SA, HvP.
          pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
          rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
        + apply HKR. rewrite ED.
          pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
          replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
          replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
          2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
              rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
          rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
    + apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
      destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
        [|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
      assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
      destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
      * injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
      * destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
        apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
        destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
        exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
        cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
        replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
        apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
    + clear H8. destruct (Z.leb 1 n) eqn:H1.
      * apply Z.leb_le in H1.
        destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
        destruct scs; [|discriminate].
        destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
        injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
        eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
      * injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
        exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sr_vars_lt_fresh : forall rs sr nx b,
  AP.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> AP.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
  induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
  apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
  ext_list (ext_call E nx R') (nx + NCS) vals.

Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
  intros E nx R' vals. unfold ext_call2.
  destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
  split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

Lemma ext_call2_at : forall E nx R' vals i, (i < length vals)%nat ->
  ev (ext_call2 E nx R' vals) (nx + NCS + i) = nth i vals (Z_to_bv 64 0).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

(* [comment removed for export] *)
Lemma reg_sound : forall E cs R n,
  regs_ok E (s_regs (a_ss cs)) R -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof.
  intros E cs R n HR Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))). unfold sr_get, reg.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.

Lemma reg_lit_sound : forall E cs R n z,
  regs_ok E (s_regs (a_ss cs)) R -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof.
  intros E cs R n z HR Hn H. unfold reg_lit, lit_of in H.
  destruct (reg cs n) as [z0| | | | | | |] eqn:Hr; try discriminate. injection H as <-.
  rewrite (reg_sound E cs R n HR Hn), Hr. cbn [edenot]. split.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, two64. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
  - unfold two64. apply Z.mod_pos_bound. lia.
Qed.

Lemma ret_lit_sound : forall E cs R r,
  regs_ok E (s_regs (a_ss cs)) R -> ret_lit cs = Some r ->
  getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64 /\ r mod 2 = 0.
Proof.
  intros E cs R r HR H. unfold ret_lit in H.
  destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
  destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
  apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
  apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
  pose proof (reg_sound E cs R 1 HR ltac:(lia)) as R1.
  rewrite Hr in R1. cbn [edenot] in R1.
  split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.

Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
  intros e b k m H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
  lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
  intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma wbytes_fill_at : forall M (s : word) b n i,
  bv_unsigned s + n <= 2 ^ 64 -> 0 <= i < n ->
  wbytes M s (repeat b (Z.to_nat n)) (Z_to_bv 64 (bv_unsigned s + i)) = Some b.
Proof.
  intros M s b n i Hnw Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
  intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma k0_sound : forall SEGS A E M k db dk ne dst k0,
  know_ok SEGS E M k ->
  (if off_image_x A k db dk ne then Some k
   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
  know_ok SEGS E M k0.
Proof.
  intros SEGS A E M k db dk ne dst k0 HK H.
  destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
  destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
  apply kimg_cut_sound. exact HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section GCall.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.

(* [comment removed for export] *)
Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation cfg := (cfgF SEGS).

(* [comment removed for export] *)
Lemma wview_rd1 : segs_wr_ok -> forall M (a : word) b,
  wview SEGS M a = Some b ->
  (match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
  intros SEGS_wr M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
  unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
  destruct (seg_writable seg) eqn:Hw; [|discriminate].
  rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : segs_wr_ok -> forall n M (a : word),
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  store_ok SEGS M a n = true ->
  exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
Proof.
  intros SEGS_wr. induction n as [|n IH]; intros M a Hnw Hst.
  - exists []. split; reflexivity.
  - cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
    cbn [rdn]. rewrite (wview_rd1 SEGS_wr M a b Hv).
    destruct n as [|n'].
    + exists [b]. split; reflexivity.
    + assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
      rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma gcall_core : forall cs E E' fx fx' R M model T (ret : Z) sr2 k' nx2 regs' M',
  cs_ok E cs fx R M model ->
  fresh_ok nx0 cs = true ->
  env_agree (nxt cs) E E' ->
  msteps SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
              (mkstF fx' regs' (Z_to_bv 64 ret) M' (seg_rom SEGS)) ->
  FXOK fx' ->
  (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a /\ M' a <> None) ->
  regs_ok E' sr2 regs' ->
  know_ok SEGS E' M' k' ->
  (forall fx'' R' M'' model',
      cs_ok E' (with_ss cs (mk_ss ret sr2 k' nx2)) fx'' R' M'' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx'' R' ret M'' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros cs E E' fx fx' R M model T ret sr2 k' nx2 regs' M' HC Hfresh Hag Hms HFX Hown HR' HK' Hk.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  unfold cfgF.
  eapply RZ_msteps; [exact (co_halt HC) | exact (co_lazy HC) | exact Hms |].
  apply (Hk fx' regs' M' model); [|reflexivity].
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | exact HR' | reflexivity | exact HK' | exact HFX |].
  intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)). exact (Hown a Ha).
Qed.

(* [comment removed for export] *)
Lemma gcall_node_sound : forall cs cs' E fx fx' R M model T (ret : Z) rv k' regs' M',
  cs_ok E cs fx R M model ->
  after_call nx0 cs ret rv k' = Some cs' ->
  msteps SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
              (mkstF fx' regs' (Z_to_bv 64 ret) M' (seg_rom SEGS)) ->
  FXOK fx' ->
  (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a /\ M' a <> None) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS E M' k' ->
  (forall E' fx'' R' M'' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx'' R' M'' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx'' R' (pc cs') M'' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros cs cs' E fx fx' R M model T ret rv k' regs' M' HC Hac Hms HFX Hown Hkept Hrv HK' Hk.
  unfold after_call in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call E (nxt cs) regs').
  pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  eapply (gcall_core cs E E' fx fx' R M model T ret _ k' _ regs' M' HC Hfresh Hag Hms HFX Hown).
  - apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs HC) Fsr Hkept).
    destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
  - eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
  - intros fx'' R' M'' model' HC' Hfs. apply (Hk E' fx'' R' M'' model'); [| exact HC' | exact Hfs].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

(* [comment removed for export] *)
Lemma gcall_node_sound2 : forall cs cs' E fx fx' R M model T (ret : Z) rv k' extra vals regs' M',
  cs_ok E cs fx R M model ->
  after_call2 nx0 cs ret rv k' extra = Some cs' ->
  msteps SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
              (mkstF fx' regs' (Z_to_bv 64 ret) M' (seg_rom SEGS)) ->
  FXOK fx' ->
  (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a /\ M' a <> None) ->
  kept_ok R regs' ->
  match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
  know_ok SEGS (ext_call2 E (nxt cs) regs' vals) M' k' ->
  (forall E' fx'' R' M'' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx'' R' M'' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx'' R' (pc cs') M'' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros cs cs' E fx fx' R M model T ret rv k' extra vals regs' M' HC Hac Hms HFX Hown Hkept Hrv HK' Hk.
  unfold after_call2 in Hac.
  match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
  injection Hac as <-.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := ext_call2 E (nxt cs) regs' vals).
  pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
  set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
  assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
  { subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
    unfold caller_saved, NCS. cbn [length]. lia. }
  assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
  { eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
    - destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
    - subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs HC) Fsr Hkept).
      destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
  eapply (gcall_core cs E E' fx fx' R M model T ret _ k' _ regs' M' HC Hfresh Hag Hms HFX Hown HR2 HK').
  intros fx'' R' M'' model' HC' Hfs. apply (Hk E' fx'' R' M'' model'); [| exact HC' | exact Hfs].
  split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

End GCall.
End GCL.
End GlzCallLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzNodesLibc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts GlzKnowLib GlzCallLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Module GNL.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kept_nat : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Ltac in_lit := cbn; repeat first [left; reflexivity | right].

Lemma reg_cases_nat : forall i, (i < 32)%nat -> i = 0%nat \/ In i caller_saved \/ In i kept_nat.
Proof.
  intros i Hi. unfold caller_saved, kept_nat.
  do 32 (destruct i as [|i]; [ first [left; reflexivity | right; left; solve [in_lit] | right; right; solve [in_lit]] |]). lia.
Qed.

(* [comment removed for export] *)
Lemma kept_ok_of : forall regs regs',
  (forall i, In i kept_nat -> getr regs' (Z_to_bv 5 (Z.of_nat i)) = getr regs (Z_to_bv 5 (Z.of_nat i))) ->
  kept_ok regs regs'.
Proof.
  intros regs regs' H r Hr0 Hn.
  destruct (reg_cases_nat (ridx r) (ridx_range r)) as [H0|[Hc|Hk]].
  - exfalso. apply Hr0. rewrite (reg_of_ridx r 0%nat H0). apply bv_eq. reflexivity.
  - exfalso. exact (Hn Hc).
  - rewrite (reg_of_ridx r (ridx r) eq_refl). apply H. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma keeps_kept_ok : forall regs regs', keeps regs regs' -> kept_ok regs regs'.
Proof.
  intros regs regs' K. apply kept_ok_of. intros i Hi. apply K. unfold kept_nat in Hi. unfold callee_kept.
  cbn in Hi. repeat (destruct Hi as [<-|Hi]; [solve [cbn; repeat first [left; apply bv_eq; reflexivity | right]] |]).
  destruct Hi.
Qed.


(* [comment removed for export] *)
Lemma keeps_cs_kept_ok : forall regs regs', keeps_cs regs regs' -> kept_ok regs regs'.
Proof.
  intros regs regs' K. apply kept_ok_of. intros i Hi. apply K. unfold kept_nat in Hi. unfold MemsetLibF.RefMemcpyLib.callee_saved.
  cbn in Hi. repeat (destruct Hi as [<-|Hi]; [solve [cbn; repeat first [left; apply bv_eq; reflexivity | right]] |]).
  destruct Hi.
Qed.

Section Specs.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fill_spec (entry cmax : Z) : Prop :=
  forall (fx : FX) mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
    0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
    store_ok SEGS mem0 s (Z.to_nat n) = true ->
    bv_unsigned c < cmax ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkstF fx regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = s.

(* [comment removed for export] *)
Definition copy_spec (entry : Z) : Prop :=
  forall (fx : FX) mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n -> length bs = Z.to_nat n ->
    rdn SEGS mem0 src (length bs) = Some bs ->
    store_ok SEGS mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkstF fx regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition move_spec (entry : Z) : Prop :=
  forall (fx : FX) mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    0 <= n < 2 ^ 63 -> length bs = Z.to_nat n ->
    (forall i, 0 <= i < n -> mem0 (Z_to_bv 64 (bv_unsigned src + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
    store_ok SEGS mem0 dst (Z.to_nat n) = true ->
    bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkstF fx regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

(* [comment removed for export] *)
Definition strlen_lit_spec (entry a len rolo rohi : Z) : Prop :=
  forall (fx : FX) mem0 (regs : bvmap 5 word) (ret : word),
    (forall x : word, rolo <= bv_unsigned x < rohi -> mem0 x = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 10%bv = Z_to_bv 64 a ->
    exists regs',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
                  (mkstF fx regs' ret mem0 (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 len.
End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wbytes_touch : forall bs M (s a : word),
  bv_unsigned s + Z.of_nat (length bs) <= 2 ^ 64 ->
  wbytes M s bs a <> M a ->
  bv_unsigned s <= bv_unsigned a < bv_unsigned s + Z.of_nat (length bs) /\ wbytes M s bs a <> None.
Proof.
  intros bs M s a Hnw Hne.
  destruct (Z_lt_dec (bv_unsigned a) (bv_unsigned s)) as [Hlt|Hge].
  { exfalso. apply Hne. apply wbytes_out; [exact Hnw | lia]. }
  destruct (Z_lt_dec (bv_unsigned a) (bv_unsigned s + Z.of_nat (length bs))) as [Hin|Hout].
  2: { exfalso. apply Hne. apply wbytes_out; [exact Hnw | lia]. }
  split; [lia|].
  replace a with (Z_to_bv 64 (bv_unsigned s + Z.of_nat (Z.to_nat (bv_unsigned a - bv_unsigned s)))).
  - apply wbytes_defined; [exact Hnw | lia].
  - rewrite Z2Nat.id by lia. replace (bv_unsigned s + (bv_unsigned a - bv_unsigned s)) with (bv_unsigned a) by lia.
    apply Z_to_bv_bv_unsigned.
Qed.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
(* [comment removed for export] *)
Hypothesis SEGS_wr : segs_wr_ok SEGS.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).
#[local] Notation cfg := (cfgF SEGS).
#[local] Notation gcall1 := (gcall_node_sound SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps).
#[local] Notation gcall2 := (gcall_node_sound2 SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps).

(* [comment removed for export] *)
Definition dst_range_owned (E : env) (cs : acs) : Prop :=
  forall a : word,
    uE E (reg cs 10) <= bv_unsigned a < uE E (reg cs 10) + uE E (reg cs 12) ->
    owned SWIN PERMc SPTOPc (blocks_den E (a_vis cs)) a.

(* [comment removed for export] *)
Lemma regs10_12 : forall E cs R, regs_ok E (s_regs (a_ss cs)) R ->
  getr R 10%bv = edenot E (reg cs 10) /\ getr R 11%bv = edenot E (reg cs 11) /\ getr R 12%bv = edenot E (reg cs 12).
Proof.
  intros E cs R HR.
  pose proof (reg_sound E cs R 10 HR ltac:(lia)) as R10. pose proof (reg_sound E cs R 11 HR ltac:(lia)) as R11.
  pose proof (reg_sound E cs R 12 HR ltac:(lia)) as R12.
  split; [exact R10 | split; [exact R11 | exact R12]].
Qed.

(* [comment removed for export] *)
Lemma summary_fill_gsound : forall entry cmax cs cs' E fx R M model T,
  fill_spec SEGS entry cmax ->
  cs_ok E cs fx R M model ->
  dst_range_owned E cs ->
  summary_fill A nx0 cs entry cmax = Some cs' ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros entry cmax cs cs' E fx R M model T SUM HC HOWN Hn Hk.
  pose proof (co_know HC) as HKN. pose proof (co_regs HC) as HREGS.
  rewrite summary_fill_eq in Hn. (* [comment removed for export] *) unfold summary_fill_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
  destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
  unfold dst_range_owned, uE in HOWN.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
  destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R ret HREGS Hret) as (R1 & Hrok & Hretr & _).
  destruct (reg_lit_sound E cs R 11 c HREGS ltac:(lia) H11) as [R11 Hc].
  destruct (regs10_12 E cs R HREGS) as (R10 & _ & R12).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
  set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.
  fold s nw n in HOWN.
  (* [comment removed for export] *)
  assert (FIN : forall k',
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     RZ (cfg fx R (pc cs) M model) T).
  { intros k' Hst HK' Hac.
    destruct (SUM fx M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
                 ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
      as (regs' & Hms & Hkept & Ha0).
    rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
    eapply (gcall1 cs cs' E fx fx R M model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact (co_fx HC).
    - intros a Ha.
      assert (Hlr : length (repeat (Z_to_bv 8 c) (Z.to_nat n)) = Z.to_nat n) by apply repeat_length.
      destruct (wbytes_touch (repeat (Z_to_bv 8 c) (Z.to_nat n)) M s a ltac:(rewrite Hlr; lia) Ha) as [Hin Hdef].
      rewrite Hlr in Hin. split; [apply HOWN; lia | exact Hdef].
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
  assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
  { apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
    rewrite Hse, Hlen in *.
    assert (Hsame : wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M).
    { destruct (Z.eq_dec n 0) as [Hz|Hnz]; [exact (WB0 Hz)|].
      assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
      rewrite wbytes_same; [reflexivity | rewrite repeat_length; lia |].
      intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
      rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
    apply (FIN (kn cs)); [apply Wst; lia | rewrite Hsame; exact HKN | exact Hn]. }
  clear Hzb.
  (* [comment removed for export] *)
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound SEGS A E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
  destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
  rewrite Hse, Hlen in *.
  eapply FIN; [apply Wst; lia | | exact Hn].
  set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
  assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
  { eapply know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
    assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
    subst M'. apply wbytes_out; rewrite repeat_length; lia. }
  destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
  assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
  assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
  { intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
  constructor; [|exact HK1].
  destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
  - apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
  - split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma summary_copy_gsound : forall entry cs cs' E fx R M model T,
  copy_spec SEGS entry ->
  cs_ok E cs fx R M model ->
  dst_range_owned E cs ->
  summary_copy SEGS A nx0 cs entry = Some cs' ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros entry cs cs' E fx R M model T SUM HC HOWN Hn Hk.
  pose proof (co_know HC) as HKN. pose proof (co_regs HC) as HREGS.
  rewrite summary_copy_eq in Hn. (* [comment removed for export] *) unfold summary_copy_ref in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (regs10_12 E cs R HREGS) as (R10 & R11 & R12).
  unfold dst_range_owned, uE in HOWN.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R ret HREGS Hret) as (R1 & Hrok & Hretr & _).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  fold s nw n in HOWN.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     rdn SEGS M sr (length bs) = Some bs ->
     store_ok SEGS M s (length bs) = true ->
     (bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     RZ (cfg fx R (pc cs) M model) T).
  { intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
    destruct (SUM fx M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    eapply (gcall1 cs cs' E fx fx R M model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact (co_fx HC).
    - intros a Ha.
      destruct (wbytes_touch bs M s a ltac:(rewrite Hlbs; lia) Ha) as [Hin Hdef].
      rewrite Hlbs in Hin. split; [apply HOWN; lia | exact Hdef].
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
  match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
  pose proof (k0_sound SEGS A E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
  apply andb_prop in Hwa as [Hwr Hap].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  (* [comment removed for export] *)
  assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
            know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
  { intros bs Hlbs Hpos.
    assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
    eapply know_ok_havoc; [exact HK0 | | apply wbytes_grows].
    intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
    apply wbytes_out; rewrite Hlbs; lia. }
  (* [comment removed for export] *)
  assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  (* [comment removed for export] *)
  assert (VARS : fresh_ok nx0 cs = true ->
            AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
            /\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
  { intros Hfresh. destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & _).
    split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
    eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
  (* [comment removed for export] *)
  assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
    forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
    after_call2 nx0 cs ret (Some (reg cs 10))
      (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
       ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
      = Some cs' ->
    RZ (cfg fx R (pc cs) M model) T).
  { intros Hswr Hsfl W u HW Hu Hac.
    destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
    destruct (flat_x_sound SEGS E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
    rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
    change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
    destruct (HusD Spos Slo Shi) as [Hus Husr].
    destruct (store_ok_rdn SEGS SEGS_wr (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
    assert (Hfresh : fresh_ok nx0 cs = true).
    { unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
    destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
    destruct (SUM fx M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
                 ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
    eapply (gcall2 cs cs' E fx fx R M model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
    - rewrite Hpc. exact Hms.
    - exact (co_fx HC).
    - intros a Ha.
      destruct (wbytes_touch bs M s a ltac:(rewrite Hlbs; lia) Ha) as [Hin Hdef].
      rewrite Hlbs in Hin. split; [apply HOWN; lia | exact Hdef].
    - exact Hkept.
    - exact Ha0.
    - set (E2 := ext_call2 E (nxt cs) regs' vals).
      pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
      assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
      assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
      assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
      assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
      pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
      apply Forall_app. split.
      + (* [comment removed for export] *)
        apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
        assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
        { unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
        cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
        rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
        subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
        assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
        rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
        pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
        pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
        replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
        apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
        rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
      + apply Forall_app. split.
        { (* [comment removed for export] *)
          unfold kblob_prefix.
          destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
          apply find_some in HF as [HinK HKt].
          destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
          apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
          apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
          pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
          assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
          rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
          change (estart E (SA sb sk)) with S in Bflat, Bbytes.
          destruct Hag2 as [Hag2a Heb2].
          assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
            [| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
          cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
          refine (conj _ (conj Blen _)).
          - unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
            change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
          - intros i Hi. rewrite <- Hus.
            replace i with (Z.of_nat (Z.to_nat i)) by lia.
            rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
            f_equal.
            pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
            rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
            cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
          }
      (* [comment removed for export] *)
        assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
        pose proof (k0_sound SEGS A E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
        assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
        { eapply know_ok_havoc; [exact HK02 | | apply wbytes_grows].
          intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
        destruct u; [|exact HAV2].
        constructor; [|exact HAV2].
        (* [comment removed for export] *)
        apply know_ok_unk_intro_pt.
        * unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
        * intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
          replace i with (Z.of_nat (Z.to_nat i)) by lia.
          apply wbytes_defined; rewrite Hlbs; lia.
    - exact Hk. }
  (* [comment removed for export] *)
  assert (HSRC :
    (if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
     then after_call2 nx0 cs ret (Some (reg cs 10))
            (map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
                 (seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
             ++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
            (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
     else None) = Some cs' ->
    RZ (cfg fx R (pc cs) M model) T).
  { destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
    apply andb_prop in Hsw as [Hswr Hsfl].
    assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
    destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
    - apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
      apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
      apply (GEN Hswr Hsfl); [|exact Hu].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - apply (GEN Hswr Hsfl); [lia | exact Hu]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
  { apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
    destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
    rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
    destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
    apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
      [apply repeat_length | | | lia | | exact Hn].
    - rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
    - rewrite repeat_length. apply Wst. lia.
    - constructor; [| apply HAVOC; [apply repeat_length | lia]].
      cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
      intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
  clear Hzs.
  (* [comment removed for export] *)
  destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
  apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
  destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
  assert (Hnn : n = nhi).
  { cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
  destruct (flat_x_sound SEGS E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
  change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
  destruct (HusD Spos Slo Shi) as [Hus Husr].
  destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
              ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
              ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
    as (bs & Hlbs & Hrd & HKC).
  change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
  rewrite <- Hnn in Hlbs, Hrd, HKC.
  apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
  - rewrite Hlbs, <- Hsre. exact Hrd.
  - rewrite Hlbs. apply Wst. lia.
  - apply Forall_app. split.
    + apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
    + apply HAVOC; [exact Hlbs | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dst_owned_range : forall E cs fx R M model,
  cs_ok E cs fx R M model -> dst_owned cs = true -> dst_range_owned E cs.
Proof.
  intros E cs fx R M model HC H a Ha.
  exact (dst_owned_sound SEGS SWIN PERMc SPTOPc E M cs a (co_know HC) H (co_perm HC) (co_top HC) (co_floor HC) Ha).
Qed.

Theorem node_memset_sound :
  fill_spec SEGS (g_memset G) two64 -> OBL_memset SEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros SUM cs cs' E fx R M model T HC _ Hn Hk. unfold node_memset in Hn.
  destruct (dst_owned cs) eqn:Hd; [|discriminate].
  exact (summary_fill_gsound (g_memset G) two64 cs cs' E fx R M model T SUM HC
           (dst_owned_range E cs fx R M model HC Hd) Hn Hk).
Qed.

Theorem node_memcpy_sound :
  copy_spec SEGS (g_memcpy G) -> OBL_memcpy SEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros SUM cs cs' E fx R M model T HC _ Hn Hk. unfold node_memcpy in Hn.
  destruct (dst_owned cs) eqn:Hd; [|discriminate].
  exact (summary_copy_gsound (g_memcpy G) cs cs' E fx R M model T SUM HC
           (dst_owned_range E cs fx R M model HC Hd) Hn Hk).
Qed.

End Sound.
End GNL.
End GlzNodesLibc.
Module GlzNodesBlob.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.   (* [comment removed for export] *)
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts GlzKnowLib GlzCallLib GlzNodesLibc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL.
Open Scope Z_scope.

Module GNB.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Defs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable G : gtable.

(* [comment removed for export] *)
Definition xt_shift (ts : xterms) (n : Z) : xterms :=
  match ts with
  | (e, c) :: r => (e, c + n) :: r
  | [] => [(ELit 0, n)]
  end.

(* [comment removed for export] *)
Definition cdiffx (k : list kentry) (x1 x2 : xterms) : option Z :=
  let n := xt_const x1 - xt_const x2 in
  if (lin_ge0 k x1 (xt_shift x2 n) && lin_ge0 k (xt_shift x2 n) x1)%bool then Some n else None.

(* [comment removed for export] *)
Definition blob_len_ok (k : list kentry) (len ne : expr) : bool :=
  expr_eqb len ne || respell_ok k ne len
  || match cdiffx k [(ne, 0)] [(len, 0)] with Some 0 => true | _ => false end.

(* [comment removed for export] *)
Definition blob_at (k : list kentry) (sb : expr) (sk : Z) (ne : expr) : option (expr * nat) :=
  match List.find (fun K => match K with
                            | KBlob (SA b o) len _ => expr_eqb b sb && Z.eqb o sk && blob_len_ok k len ne
                            | _ => false
                            end) k with
  | Some (KBlob _ len j) => Some (len, j)
  | _ => None
  end.

(* [comment removed for export] *)
Definition xt_ok (k : list kentry) (b : expr) (o : Z) : bool :=
  match xlo k b, xhi k b with
  | Some l, Some h => Z.leb 0 (l + o) && Z.ltb (h + o) two64
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition node_memcpy_blob (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (g_memcpy G)) then None else
  if negb (dst_owned cs) then None else
  match ret_lit cs with
  | None => None
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            match blob_at k sb sk ne with
            | None => None
            | Some (len, j) =>
                if (off_image_x A k db dk ne && kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne
                    && xt_ok k db dk)%bool
                then after_call nx0 cs ret (Some dst)
                       (KBlob (SA db dk) len j :: KUnk (SA db dk) ne :: kn_havoc k db dk ne)
                else None
            end
          else None
      | _, _, _, _ => None
      end
  end.

(* [comment removed for export] *)
Definition GMAX : Z := 4096.

Definition lit_piece (zs : list Z) : list spiece :=
  match zs with [] => [] | _ => [SPLit zs] end.

(* [comment removed for export] *)
Fixpoint gather_blob (k : list kentry) (facts : list kentry) (b : expr) (o : Z) (hb : expr) (ho : Z)
  : option (list spiece) :=
  match facts with
  | [] => None
  | KBlob (SA fb fo) len j :: rest =>
      match (match cdiffx k [(fb, fo)] [(b, o)], cdiffx k [(hb, ho)] [(fb, fo); (len, 0)] with
             | Some np, Some ns =>
                 if (Z.leb 0 np && Z.leb np GMAX && Z.leb 0 ns && Z.leb ns GMAX)%bool then
                   match kread_bytes segs (Z.to_nat np) k b o, kread_bytes segs (Z.to_nat ns) k hb (ho - ns) with
                   | Some zs1, Some zs2 => Some (lit_piece zs1 ++ SPBlob j :: lit_piece zs2)
                   | _, _ => None
                   end
                 else None
             | _, _ => None
             end)
      with
      | Some ps => Some ps
      | None => gather_blob k rest b o hb ho
      end
  | _ :: rest => gather_blob k rest b o hb ho
  end.

Definition kgather (k : list kentry) (lo hi : expr) : option (list spiece) :=
  let '(b, o) := split_lit lo in let '(hb, ho) := split_lit hi in
  if negb (xt_ok k b o && xt_ok k hb ho)%bool then None else
  match (match cdiffx k [(hb, ho)] [(b, o)] with
         | Some n =>
             if (Z.leb 0 n && Z.leb n GMAX)%bool then
               match kread_bytes segs (Z.to_nat n) k b o with Some zs => Some (lit_piece zs) | None => None end
             else None
         | None => None
         end) with
  | Some ps => Some ps
  | None => gather_blob k k b o hb ho
  end.
End Defs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Helpers.
Variable SEGS : list Segment.

Lemma xt_shift_den : forall E ts n, xt_den E (xt_shift ts n) = xt_den E ts + n.
Proof.
  intros E [|[e c] r] n; cbn [xt_shift xt_den].
  - rewrite edenot_lit, u64_lit by (unfold two64; lia). lia.
  - lia.
Qed.

Lemma cdiffx_sound : forall E M k x1 x2 n,
  know_ok SEGS E M k -> cdiffx k x1 x2 = Some n -> xt_den E x1 = xt_den E x2 + n.
Proof.
  intros E M k x1 x2 n HK H. unfold cdiffx in H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection H as <-. apply andb_prop in Hc as [H1 H2].
  pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as L1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as L2.
  rewrite xt_shift_den in L1, L2. lia.
Qed.

Lemma xt_den1 : forall E e c, xt_den E [(e, c)] = uE E e + c.
Proof. intros E e c. cbn [xt_den]. unfold uE. lia. Qed.

Lemma xt_den2 : forall E e c e' c', xt_den E [(e, c); (e', c')] = uE E e + c + (uE E e' + c').
Proof. intros E e c e' c'. cbn [xt_den]. unfold uE. lia. Qed.

Lemma blob_len_ok_sound : forall E M k len ne,
  know_ok SEGS E M k -> blob_len_ok k len ne = true -> edenot E len = edenot E ne.
Proof.
  intros E M k len ne HK H. unfold blob_len_ok in H.
  apply orb_prop in H as [H|H].
  - apply orb_prop in H as [H|H].
    + apply expr_eqb_eq in H. subst. reflexivity.
    + symmetry. exact (respell_ok_sound SEGS E M k ne len HK H).
  - destruct (cdiffx k [(ne, 0)] [(len, 0)]) as [d|] eqn:Hd; [|discriminate].
    destruct d; try discriminate.
    pose proof (cdiffx_sound E M k _ _ _ HK Hd) as Hx. rewrite !xt_den1 in Hx. unfold uE in Hx.
    apply bv_eq. lia.
Qed.

Lemma blob_at_sound : forall k sb sk ne len j,
  blob_at k sb sk ne = Some (len, j) -> In (KBlob (SA sb sk) len j) k /\ blob_len_ok k len ne = true.
Proof.
  intros k sb sk ne len j H. unfold blob_at in H.
  destruct (List.find _ k) as [K|] eqn:HF; [|discriminate].
  apply find_some in HF as [Hin Ht].
  destruct K as [| |[kb ko] klen kj| | | | | | |]; try discriminate.
  injection H as <- <-.
  apply andb_prop in Ht as [Ht Hl]. apply andb_prop in Ht as [Hb Ho].
  apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. subst. split; [exact Hin | exact Hl].
Qed.

Lemma xt_ok_sound : forall E M k b o,
  know_ok SEGS E M k -> xt_ok k b o = true -> 0 <= estart E (SA b o) < 2 ^ 64.
Proof.
  intros E M k b o HK H. unfold xt_ok in H.
  destruct (xlo k b) as [l|] eqn:Hl; [|discriminate]. destruct (xhi k b) as [h|] eqn:Hh; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (xlo_sound SEGS E M k b l HK Hl). pose proof (xhi_sound SEGS E M k b h HK Hh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_list : forall m (bs : list byte) (a : Z),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  rdn SEGS m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m bs. induction bs as [|x bs IH]; intros a Ha Hhi Hall; [reflexivity|].
  cbn [length] in Hhi, Hall. cbn [length rdn].
  pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [Z.to_nat nth] in H0. rewrite H0.
  assert (Ha1 : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
    change (bv_unsigned (1 : word)) with 1. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
  rewrite Ha1, (IH (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. rewrite (Hall (i + 1)) by lia.
  f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma Z_to_bv_add_nat : forall a n, (Z_to_bv 64 a + nat_to_word n)%bv = Z_to_bv 64 (a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, <- Z.add_mod by lia. reflexivity.
Qed.

Lemma lit_piece_den : forall E zs, flat_map (piece_den E) (lit_piece zs) = map (Z_to_bv 8) zs.
Proof. intros E [|z zs]; cbn; [reflexivity | rewrite app_nil_r; reflexivity]. Qed.

Lemma pieces3_den : forall E zs1 j zs2,
  flat_map (piece_den E) (lit_piece zs1 ++ SPBlob j :: lit_piece zs2) = map (Z_to_bv 8) zs1 ++ eb E j ++ map (Z_to_bv 8) zs2.
Proof.
  intros E zs1 j zs2. rewrite flat_map_app. cbn [flat_map]. rewrite !lit_piece_den. cbn [piece_den]. reflexivity.
Qed.

Definition piece_lit_ok (p : spiece) : Prop :=
  match p with SPLit zs => Forall (fun z => 0 <= z < 256) zs | SPBlob _ => True end.

Lemma lit_piece_ok : forall zs, Forall (fun z => 0 <= z < 256) zs -> Forall piece_lit_ok (lit_piece zs).
Proof. intros [|z zs] H; cbn; [constructor | constructor; [exact H | constructor]]. Qed.

(* [comment removed for export] *)
Lemma gather_blob_sound : forall E M k facts b o hb ho ps,
  know_ok SEGS E M k -> incl facts k ->
  0 <= estart E (SA b o) < 2 ^ 64 -> 0 <= estart E (SA hb ho) < 2 ^ 64 ->
  gather_blob SEGS k facts b o hb ho = Some ps ->
  let bs := flat_map (piece_den E) ps in
  estart E (SA hb ho) = estart E (SA b o) + Z.of_nat (length bs)
  /\ rdn SEGS M (Z_to_bv 64 (estart E (SA b o))) (length bs) = Some bs
  /\ Forall piece_lit_ok ps.
Proof.
  intros E M k facts. induction facts as [|K rest IH]; intros b o hb ho ps HK Hincl Hlo Hhi H; [discriminate|].
  assert (Hrest : incl rest k) by (intros x Hx; apply Hincl; right; exact Hx).
  cbn [gather_blob] in H.
  destruct K as [| |[fb fo] len j| | | | | | |]; try exact (IH b o hb ho ps HK Hrest Hlo Hhi H).
  match type of H with (match ?inner with Some _ => _ | None => _ end) = _ =>
    destruct inner as [ps0|] eqn:Hin; [injection H as <- | exact (IH b o hb ho ps HK Hrest Hlo Hhi H)] end.
  destruct (cdiffx k [(fb, fo)] [(b, o)]) as [np|] eqn:Hnp; [|discriminate].
  destruct (cdiffx k [(hb, ho)] [(fb, fo); (len, 0)]) as [ns|] eqn:Hns; [|discriminate].
  match type of Hin with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc Hns2]. apply andb_prop in Hc as [Hc Hns1]. apply andb_prop in Hc as [Hnp1 Hnp2].
  apply Z.leb_le in Hnp1. apply Z.leb_le in Hnp2. apply Z.leb_le in Hns1. apply Z.leb_le in Hns2.
  destruct (kread_bytes SEGS (Z.to_nat np) k b o) as [zs1|] eqn:Hz1; [|discriminate].
  destruct (kread_bytes SEGS (Z.to_nat ns) k hb (ho - ns)) as [zs2|] eqn:Hz2; [|discriminate].
  injection Hin as <-.
  (* [comment removed for export] *)
  pose proof (cdiffx_sound E M k _ _ _ HK Hnp) as Xnp. rewrite !xt_den1 in Xnp.
  pose proof (cdiffx_sound E M k _ _ _ HK Hns) as Xns. rewrite xt_den1, xt_den2 in Xns.
  pose proof (Hincl _ (or_introl eq_refl)) as HinK.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HKB. cbn [kentry_ok] in HKB.
  destruct HKB as (Bflat & Blen & Bbytes).
  set (P0 := estart E (SA b o)) in *. set (P1 := estart E (SA hb ho)) in *. set (S := estart E (SA fb fo)) in *.
  set (L := elenZ E len) in *.
  assert (HS : S = P0 + np) by (subst S P0; unfold estart; cbn [a_base a_off]; unfold uE in Xnp; lia).
  assert (HP1 : P1 = S + L + ns) by (subst S P1 L; unfold estart, elenZ; cbn [a_base a_off]; unfold uE in Xns; lia).
  unfold flat in Bflat. fold S in Bflat.
  (* [comment removed for export] *)
  destruct (kread_bytes_sound SEGS E M k (Z.to_nat np) b o zs1 HK Hz1 ltac:(lia) ltac:(fold P0; lia)) as (R1 & L1 & F1).
  fold P0 in R1.
  assert (R2 : rdn SEGS M (Z_to_bv 64 S) (length (eb E j)) = Some (eb E j)).
  { apply rdn_overlay_list; [lia | lia |]. intros i Hi. apply Bbytes. lia. }
  assert (E3 : estart E (SA hb (ho - ns)) = S + L) by (unfold estart; cbn [a_base a_off]; subst P1; unfold estart in HP1; cbn [a_base a_off] in HP1; lia).
  destruct (kread_bytes_sound SEGS E M k (Z.to_nat ns) hb (ho - ns) zs2 HK Hz2 ltac:(rewrite E3; lia) ltac:(rewrite E3; lia)) as (R3 & L3 & F3).
  rewrite E3 in R3.
  (* [comment removed for export] *)
  cbn zeta. rewrite pieces3_den.
  rewrite !length_app, !length_map, L1, L3.
  split; [lia|]. split.
  - pose proof (rdn_app SEGS M (length (eb E j)) (Z_to_bv 64 S) (Z.to_nat ns) (eb E j) (map (Z_to_bv 8) zs2) R2) as RB.
    rewrite Z_to_bv_add_nat, Blen in RB. specialize (RB ltac:(exact R3)).
    pose proof (rdn_app SEGS M (Z.to_nat np) (Z_to_bv 64 P0) (length (eb E j) + Z.to_nat ns)%nat (map (Z_to_bv 8) zs1) (eb E j ++ map (Z_to_bv 8) zs2) R1) as RA.
    rewrite Z_to_bv_add_nat, Z2Nat.id, <- HS in RA by lia. specialize (RA RB).
    exact RA.
  - apply Forall_app. split; [apply lit_piece_ok; exact F1|]. constructor; [exact I|]. apply lit_piece_ok; exact F3.
Qed.

Theorem kgather_sound : forall E M k lo hi ps,
  know_ok SEGS E M k -> kgather SEGS k lo hi = Some ps ->
  let bs := flat_map (piece_den E) ps in
  uE E hi = uE E lo + Z.of_nat (length bs)
  /\ uE E lo + Z.of_nat (length bs) <= 2 ^ 64
  /\ rdn SEGS M (edenot E lo) (length bs) = Some bs
  /\ Forall piece_lit_ok ps.
Proof.
  intros E M k lo hi ps HK H. unfold kgather in H.
  destruct (split_lit lo) as [b o] eqn:Hslo. destruct (split_lit hi) as [hb ho] eqn:Hshi.
  destruct (xt_ok k b o && xt_ok k hb ho)%bool eqn:Hok; [|discriminate]. cbn [negb] in H.
  apply andb_prop in Hok as [Hok1 Hok2].
  pose proof (xt_ok_sound E M k b o HK Hok1) as Hlo. pose proof (xt_ok_sound E M k hb ho HK Hok2) as Hhi.
  assert (Ulo : uE E lo = estart E (SA b o)).
  { unfold uE. rewrite (split_lit_denot E lo b o Hslo). unfold estart. cbn [a_base a_off]. apply u64_lit.
    unfold estart in Hlo. cbn [a_base a_off] in Hlo. lia. }
  assert (Uhi : uE E hi = estart E (SA hb ho)).
  { unfold uE. rewrite (split_lit_denot E hi hb ho Hshi). unfold estart. cbn [a_base a_off]. apply u64_lit.
    unfold estart in Hhi. cbn [a_base a_off] in Hhi. lia. }
  assert (Elo : edenot E lo = Z_to_bv 64 (estart E (SA b o))).
  { rewrite (split_lit_denot E lo b o Hslo). reflexivity. }
  rewrite Ulo, Uhi, Elo.
  match type of H with (match ?first with Some _ => _ | None => _ end) = _ => destruct first as [ps0|] eqn:Hfirst end.
  - (* [comment removed for export] *)
    injection H as <-.
    destruct (cdiffx k [(hb, ho)] [(b, o)]) as [n|] eqn:Hn; [|discriminate].
    match type of Hfirst with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hn0 HnG]. apply Z.leb_le in Hn0. apply Z.leb_le in HnG.
    destruct (kread_bytes SEGS (Z.to_nat n) k b o) as [zs|] eqn:Hzs; [|discriminate]. injection Hfirst as <-.
    pose proof (cdiffx_sound E M k _ _ _ HK Hn) as Xn. rewrite !xt_den1 in Xn. unfold uE in Xn.
    assert (HP : estart E (SA hb ho) = estart E (SA b o) + n) by (unfold estart; cbn [a_base a_off]; lia).
    destruct (kread_bytes_sound SEGS E M k (Z.to_nat n) b o zs HK Hzs ltac:(lia) ltac:(lia)) as (R1 & L1 & F1).
    cbn zeta. rewrite lit_piece_den, length_map, L1, Z2Nat.id by lia.
    split; [lia|]. split; [lia|]. split; [exact R1 | apply lit_piece_ok; exact F1].
  - (* [comment removed for export] *)
    pose proof (gather_blob_sound E M k k b o hb ho ps HK (incl_refl _) Hlo Hhi H) as (G1 & G2 & G3).
    split; [exact G1|]. split; [lia|]. split; [exact G2 | exact G3].
Qed.
End Helpers.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.

#[local] Abbreviation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Abbreviation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).
#[local] Abbreviation cfg := (cfgF SEGS).
#[local] Abbreviation gcall1 := (gcall_node_sound SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps).

Theorem node_memcpy_blob_sound :
  GNL.copy_spec SEGS (g_memcpy G) -> node1_stmt always (node_memcpy_blob A nx0 G).
Proof.
  intros SUM cs cs' E fx R M model T HC _ Hn Hk. unfold node_memcpy_blob in Hn.
  pose proof (co_know HC) as HKN. pose proof (co_regs HC) as HREGS.
  destruct (Z.eqb (pc cs) (g_memcpy G)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (dst_owned cs) eqn:Hd; [|discriminate]. cbn [negb] in Hn.
  pose proof (GNL.dst_owned_range SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model HC Hd) as HOWN.
  unfold GNL.dst_range_owned, uE in HOWN.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (GNL.regs10_12 E cs R HREGS) as (R10 & R11 & R12).
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  destruct (blob_at (kn cs) sb sk ne) as [[len j]|] eqn:Hblob; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  apply andb_prop in Hchk as [Hchk Hxt]. apply andb_prop in Hchk as [Hchk Hap]. apply andb_prop in Hchk as [Hoff Hwr].
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R ret HREGS Hret) as (R1 & Hrok & Hretr & _).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  destruct (blob_at_sound (kn cs) sb sk ne len j Hblob) as [HinK Hleq].
  pose proof (blob_len_ok_sound SEGS E M (kn cs) len ne HKN Hleq) as Hlen_eq.
  pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
  destruct HKB as (Bflat & Blen & Bbytes).
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
  pose proof (xt_ok_sound SEGS E M (kn cs) db dk HKN Hxt) as HDr.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  assert (Hlen : elenZ E ne = n) by reflexivity.
  assert (HlenL : elenZ E len = n) by (unfold elenZ; rewrite Hlen_eq; reflexivity).
  rewrite HlenL in Bflat, Blen, Bbytes. rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  unfold flat in Bflat.
  pose proof (u64_range nw) as Hnr. fold n in Hnr.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (HDdef : D = bv_unsigned (edenot E db) + dk) by reflexivity.
  assert (HSdef : S = bv_unsigned (edenot E sb) + sk) by reflexivity.
  assert (Hus : bv_unsigned s = D) by (rewrite Hsd, <- HDdef; apply u64_lit; lia).
  assert (Husr : bv_unsigned sr = S) by (rewrite Hss, <- HSdef; apply u64_lit; lia).
  assert (HsD : s = Z_to_bv 64 D) by (rewrite <- Hus, Z_to_bv_bv_unsigned; reflexivity).
  assert (HsrS : sr = Z_to_bv 64 S) by (rewrite <- Husr, Z_to_bv_bv_unsigned; reflexivity).
  fold s nw n in HOWN.
  (* [comment removed for export] *)
  set (bs := eb E j) in *.
  assert (Hlbs : length bs = Z.to_nat n) by lia.
  assert (Hrd : rdn SEGS M sr (length bs) = Some bs).
  { rewrite HsrS. apply rdn_overlay_list; [lia | lia |]. intros i Hi. apply Bbytes. lia. }
  assert (Hst : store_ok SEGS M s (length bs) = true) by (rewrite HsD, Hlbs; apply Wst; lia).
  destruct (SUM fx M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
               ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
  eapply (gcall1 cs cs' E fx fx R M model T ret (Some (reg cs 10)) _ regs' (wbytes M s bs) HC Hn).
  - rewrite Hpc. exact Hms.
  - exact (co_fx HC).
  - intros a Ha.
    destruct (GNL.wbytes_touch bs M s a ltac:(rewrite Hlbs; lia) Ha) as [Hin Hdef].
    rewrite Hlbs in Hin. split; [apply HOWN; lia | exact Hdef].
  - exact Hkept.
  - exact Ha0.
  - (* [comment removed for export] *)
    assert (Hhit : forall i, 0 <= i < n -> wbytes M s bs (Z_to_bv 64 (D + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    { intros i Hi. rewrite <- Hus. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite Nat2Z.id.
      rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia). reflexivity. }
    constructor.
    { (* [comment removed for export] *)
      cbn [kentry_ok]. rewrite HlenL. fold D bs. split; [unfold flat; lia|]. split; [lia|]. exact Hhit. }
    constructor.
    { (* [comment removed for export] *)
      apply know_ok_unk_intro_pt; [unfold flat; rewrite Hlen; fold D; lia|].
      intros i Hi. rewrite Hlen in Hi. fold D. rewrite Hhit by lia. discriminate. }
    (* [comment removed for export] *)
    eapply know_ok_havoc; [exact HKN | | apply wbytes_grows].
    intros x Hx. fold D in Hx. rewrite Hlen in Hx. apply wbytes_out; rewrite Hlbs; lia.
  - exact Hk.
Qed.

End Sound.
End GNB.
End GlzNodesBlob.
Module DrvNodes2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzNodesBlob DrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Module DN2.
Import DN.
Section Nodes.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
Definition file_syms (k : list kentry) (f : Z) : option (Z * expr * expr * expr * expr) :=
  match kreadZ segs k (ELit 0) (f + 120) 4, kread8e segs k (ELit 0) (f + 88), kread8e segs k (ELit 0) (f + 96),
        kread8e segs k (ELit 0) (f + 56), kread8e segs k (ELit 0) (f + 40) with
  | Some fd, Some buf, Some bsz, Some wb, Some wp => Some (fd, buf, bsz, wb, wp)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)

Definition node_stdio_write2 (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_STDIO_WRITE) then None else
  let k := kn cs in
  match reg_lit cs 10, ret_lit cs with
  | Some f, Some ret =>
      if negb ((Z.eqb f FILE1 || Z.eqb f FILE2) && sp_ok cs FR_SW && frame_ok cs FR_SW && ssp_ok segs k && fresh_ok nx0 cs
               && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then None else
      match file_syms k f with
      | Some (fd, buf, bsz, wb, wp) =>
          if negb ((Z.eqb fd 1 && Z.eqb f FILE1) || (Z.eqb fd 2 && Z.eqb f FILE2))%bool then None else
          let s := reg cs 11 in let l := reg cs 12 in
          let '(wbb, wbk) := split_lit wb in let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
          match GNB.kgather segs k wb wp, GNB.kgather segs k s (eadd s l) with
          | Some pend, Some ext =>
              (* [comment removed for export] *)
              let ok := (lin_ge0 k [(ELit 0, SPHI)] [(wp, 0)] && lin_ge0 k [(ELit 0, SPHI)] [(s, 0); (l, 0)]
                         && lin_ge0 k [(wb, 2 ^ 30)] [(wp, 0); (l, 0)]
                         && bflat_x k wbb wbk (esub wp wb) && disj_x k wbb wbk (esub wp wb) spb (spk - FR_SW) (ELit FR_SW)
                         && bflat_x k sb sk l && disj_x k sb sk l spb (spk - FR_SW) (ELit FR_SW))%bool in
              if negb ok then None else
              let k1 := kn_havoc k spb (spk - FR_SW) (ELit FR_SW) in
              let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 32) in
              let k3 := [KWord (SA (ELit 0) (f + 32)) 8 (eadd buf bsz); KWord (SA (ELit 0) (f + 40)) 8 buf;
                         KWord (SA (ELit 0) (f + 56)) 8 buf] ++ k2 in
              match after_call nx0 cs ret (Some l) k3 with
              | Some cs' => Some (fd, pend ++ ext, cs')
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition P_STRNLEN : Z := 0x6f380.
Definition FR_SNL : Z := 32.
Definition node_strnlen (nzb : list nat) (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) P_STRNLEN) then None else
  let k := kn cs in
  match reg_lit cs 11, ret_lit cs with
  | Some n, Some ret =>
      if negb (sp_ok cs FR_SNL && frame_ok cs FR_SNL && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32
               && kimg_covers k 0x13040 32 && Z.leb 0 n && Z.ltb n two64)%bool then None else
      let s := reg cs 10 in let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
      match find (fun K => match K with KBlob (SA b o) _ j => expr_eqb b sb && Z.eqb o sk && existsb (Nat.eqb j) nzb | _ => false end) k with
      | Some (KBlob _ L _) =>
          let ok := (existsb (kentry_eqb (KWord (SA (eadd s L) 0) 1 (ELit 0))) k
                     && existsb (fun K => match K with KUnk (SA b o) m => expr_eqb b sb && Z.eqb o sk && lin_ge0 k [(m, 0)] [(L, 8)] | _ => false end) k
                     && match xhi k L with Some lh => Z.leb (lh + 8) n | None => false end
                     && bflat_x k sb sk (eadd L (ELit 8))
                     && disj_x k sb sk (eadd L (ELit 8)) spb (spk - FR_SNL) (ELit FR_SNL)
                     && lin_ge0 k [(ELit 0, SPHI)] [(s, 0); (L, 8)]
                     && lin_ge0 k [(s, 0)] [(ELit 1, 0)])%bool in
          if negb ok then None else
          after_call nx0 cs ret (Some L) (kn_havoc k spb (spk - FR_SNL) (ELit FR_SNL))
      | _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_read_dir (cs : acs) : option acs :=
  match reg_lit cs 11, reg_lit cs 12 with
  | Some b, Some c =>
      if (at_sys segs cs 63 && reg_is cs 10 3 && Z.leb 0 b && Z.leb 0 c && Z.leb (b + c) (2 ^ 47))%bool
      then Some (set_pc (set_reg cs 10 (ELit (two64 - 21))) (pc cs + 4)) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition XNe (G : gtable) (nzb : list nat) (dird : bool) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 63%nat => node_ioctl segs cs
  | 1%nat => node_memcpy segs A nx0 G cs
  | 5%nat => GNB.node_memcpy_blob A nx0 G cs
  | 67%nat => node_strnlen nzb cs
  | 68%nat => if dird then node_read_dir cs else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition XEe (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 66%nat => node_stdio_write2 cs
  | _ => XEd segs nx0 id args cs
  end.
End Nodes.
End DN2.
End DrvNodes2.
Module GlzNodesMove.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts GlzKnowLib GlzCallLib GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL. Import GNL.
Open Scope Z_scope.

Module GNM.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
Hypothesis SEGS_wr : segs_wr_ok SEGS.
(* [comment removed for export] *)
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).
#[local] Notation cfg := (cfgF SEGS).
#[local] Notation gcall1 := (gcall_node_sound SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps).

(* [comment removed for export] *)
Lemma kn_readable_x_sound : forall E M k sb sk ne,
  know_ok SEGS E M k -> kn_readable_x k sb sk ne = true ->
  0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E ne <= 2 ^ 64
  /\ forall i, 0 <= i < elenZ E ne -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None.
Proof.
  intros E M k sb sk ne HK H. unfold kn_readable_x in H. apply existsb_exists in H as [K [HinK HKt]].
  pose proof (proj1 (Forall_forall _ _) HK K HinK) as HKK.
  pose proof (u64_range (edenot E ne)) as Hne. unfold elenZ in *.
  assert (GEN : forall kb kk len (P : option byte -> Prop),
            xinside k sb sk ne kb kk len = true ->
            flat E (SA kb kk) (bv_unsigned (edenot E len)) ->
            (forall i, 0 <= i < bv_unsigned (edenot E len) -> P (M (Z_to_bv 64 (estart E (SA kb kk) + i)))) ->
            (forall x, P x -> x <> None) ->
            0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + bv_unsigned (edenot E ne) <= 2 ^ 64
            /\ forall i, 0 <= i < bv_unsigned (edenot E ne) -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None).
  { intros kb kk len P Hx Hfl HP HPn.
    destruct (xinside_sound SEGS E M k sb sk ne kb kk len HK Hx) as [X1 X2]. unfold elenZ in X2.
    destruct Hfl as (F1 & F2 & F3 & F4).
    split; [lia|]. split; [lia|]. intros i Hi.
    replace (estart E (SA sb sk) + i) with (estart E (SA kb kk) + (estart E (SA sb sk) - estart E (SA kb kk) + i)) by lia.
    apply HPn. apply HP. lia. }
  destruct K as [|[kb kk] len|[kb kk] len j| | | | | |[kb kk] len c|[kb kk] len]; try discriminate; cbn [kentry_ok] in HKK; unfold elenZ in HKK.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 0))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as (Hfl & Hl & Hz). eapply (GEN kb kk len (fun x => exists b, x = Some b)); [exact HKt | exact Hfl | | intros x [b ->]; discriminate].
    intros i Hi. eexists. apply Hz. exact Hi.
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x = Some (Z_to_bv 8 c))); [exact HKt | exact Hfl | exact Hz | intros x ->; discriminate].
  - destruct HKK as [Hfl Hz]. eapply (GEN kb kk len (fun x => x <> None)); [exact HKt | exact Hfl | exact Hz | intros x Hx; exact Hx].
Qed.

Lemma src_def_x_sound : forall E M k sb sk ne,
  know_ok SEGS E M k -> src_def_x A k sb sk ne = true ->
  0 <= estart E (SA sb sk) /\ estart E (SA sb sk) + elenZ E ne <= 2 ^ 64
  /\ forall i, 0 <= i < elenZ E ne -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) <> None.
Proof.
  intros E M k sb sk ne HK H. unfold src_def_x in H. apply orb_prop in H as [H|H]; [exact (kn_readable_x_sound E M k sb sk ne HK H)|].
  destruct ne as [n| | | | | | |]; try discriminate.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H. apply Z.leb_le in X3. apply Z.leb_le in X2.
  pose proof (flat_x_sound SEGS E M k sb sk (ELit n) HK X1) as (F1 & F2 & F3).
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ _ _ _ HK X0) as AP0.
  cbn [edenot] in F2, F3. rewrite u64_lit in F2, F3 by lia.
  pose proof HULL_ok as HU; unfold APS.hull_ok, KHI in HU.
  rewrite (elenZ_lit E n) in AP0 by lia. rewrite (elenZ_lit E (img_hi A - img_lo A)) in AP0 by lia.
  unfold estart in AP0; cbn [a_base a_off edenot] in AP0. rewrite u_lit0 in AP0.
  rewrite elenZ_lit by lia. split; [unfold estart in *; cbn [a_base a_off] in *; lia|].
  split; [unfold estart in *; cbn [a_base a_off] in *; lia|].
  intros i Hi. unfold estart in *; cbn [a_base a_off] in *.
  replace (bv_unsigned (edenot E sb) + sk + i)%Z with (APS.uE E sb + (sk + i))%Z by (unfold APS.uE; lia).
  apply (cover_x_sound SEGS A SEGS_in_hull _ E M k sb sk (sk + n) HK X); [lia|].
  unfold in_hull, APS.uE. apply andb_false_iff.
  destruct AP0 as [AP0|AP0]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia].
Qed.

(* [comment removed for export] *)
Definition mbytes (M : word -> option byte) (a : word) (n : nat) : list byte :=
  map (fun j => match M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n).

Lemma mbytes_length : forall M a n, length (mbytes M a n) = n.
Proof. intros. unfold mbytes. rewrite length_map, length_seq. reflexivity. Qed.

Lemma mbytes_nth : forall M (a : word) n i,
  0 <= i < Z.of_nat n -> M (Z_to_bv 64 (bv_unsigned a + i)) <> None ->
  M (Z_to_bv 64 (bv_unsigned a + i)) = Some (nth (Z.to_nat i) (mbytes M a n) (Z_to_bv 8 0)).
Proof.
  intros M a n i Hi Hd. unfold mbytes. rewrite (nth_map_seq _ n (Z.to_nat i) (Z_to_bv 8 0)) by lia.
  rewrite Z2Nat.id by lia. destruct (M (Z_to_bv 64 (bv_unsigned a + i))) as [b|]; [reflexivity | exfalso; apply Hd; reflexivity].
Qed.

Lemma summary_move_gsound : forall entry cs cs' E fx R M model T,
  move_spec SEGS entry ->
  cs_ok E cs fx R M model ->
  dst_range_owned SWIN PERMc SPTOPc E cs ->
  summary_move A nx0 cs entry = Some cs' ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) T.
Proof.
  intros entry cs cs' E fx R M model T SUM HC HOWN Hn Hk.
  pose proof (co_know HC) as HKN. pose proof (co_regs HC) as HREGS.
  rewrite summary_move_eq in Hn. unfold summary_move_ref in Hn.   (* [comment removed for export] *)
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (regs10_12 E cs R HREGS) as (R10 & R11 & R12).
  unfold dst_range_owned, uE in HOWN.
  remember (reg cs 12) as ne eqn:Hne.
  destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
  destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
  apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.
  (* [comment removed for export] *)
  destruct (ret_lit_sound E cs R ret HREGS Hret) as (R1 & Hrok & Hretr & _).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
  set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
  set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
  assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  pose proof (split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
  pose proof (split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
  assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
  assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
  assert (Hlen : elenZ E ne = n) by reflexivity.
  fold s nw n in HOWN.
  (* [comment removed for export] *)
  assert (FIN : forall k' bs,
     length bs = Z.to_nat n ->
     (forall i, 0 <= i < n -> M (Z_to_bv 64 (bv_unsigned sr + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
     store_ok SEGS M s (Z.to_nat n) = true ->
     know_ok SEGS E (wbytes M s bs) k' ->
     after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
     RZ (cfg fx R (pc cs) M model) T).
  { intros k' bs Hlbs Hsrc Hst HK' Hac.
    destruct (SUM fx M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hsrc Hst ltac:(lia) ltac:(lia) Hrok R1 R10 R11
                 ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
    eapply (gcall1 cs cs' E fx fx R M model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
    - rewrite Hpc. exact Hms.
    - exact (co_fx HC).
    - intros a Ha.
      destruct (wbytes_touch bs M s a ltac:(rewrite Hlbs; lia) Ha) as [Hin Hdef].
      rewrite Hlbs in Hin. split; [apply HOWN; lia | exact Hdef].
    - exact Hkept.
    - exact Ha0.
    - exact HK'.
    - exact Hk. }
  (* [comment removed for export] *)
  destruct (Z.eqb nhi 0) eqn:Hnhi0.
  { apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
    apply (FIN (kn cs) []); [rewrite Hz; reflexivity | intros i Hi; lia | rewrite Hz; reflexivity | cbn [wbytes]; exact HKN | exact Hn]. }
  (* [comment removed for export] *)
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc2; [|discriminate] end.
  apply andb_prop in Hc2 as [Hc2 Hsd0]. apply andb_prop in Hc2 as [Hwr Hoff].
  destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
  destruct (src_def_x_sound E M (kn cs) sb sk ne HKN Hsd0) as (Slo & Shi & Sdef).
  rewrite Hlen in *.
  set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
  rewrite Hse in Wst.
  assert (HusD : 0 < n -> bv_unsigned s = D /\ bv_unsigned sr = S).
  { intros Hpos. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }
  set (bs := mbytes M sr (Z.to_nat n)).
  assert (Hlbs : length bs = Z.to_nat n) by apply mbytes_length.
  apply (FIN (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc (kn cs) db dk ne else kn_havoc (kn cs) db dk ne) bs Hlbs).
  - intros i Hi. destruct (HusD ltac:(lia)) as [Hus Husr].
    apply mbytes_nth; [lia|]. rewrite Husr. apply Sdef. lia.
  - apply Wst. lia.
  - assert (HAV : know_ok SEGS E (wbytes M s bs) (kn_havoc (kn cs) db dk ne)).
    { eapply know_ok_havoc; [exact HKN | | apply wbytes_grows].
      intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      { destruct bs; [reflexivity | exfalso; rewrite Hz in Hlbs; discriminate Hlbs]. }
      destruct (HusD ltac:(lia)) as [Hus _]. apply wbytes_out; rewrite Hlbs; lia. }
    destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HAV]. apply Z.ltb_lt in Hpos.
    destruct (HusD ltac:(lia)) as [Hus Husr].
    constructor; [|exact HAV].
    apply know_ok_unk_intro_pt.
    + unfold flat. rewrite Hlen. change (estart E (SA db dk)) with D. lia.
    + intros i Hi. rewrite Hlen in Hi. change (estart E (SA db dk)) with D. rewrite <- Hus.
      replace i with (Z.of_nat (Z.to_nat i)) by lia.
      apply wbytes_defined; rewrite Hlbs; lia.
  - exact Hn.
Qed.

(* [comment removed for export] *)
Theorem node_memmove_sound :
  copy_spec SEGS (g_memmove G) -> move_spec SEGS (g_memmove G) ->
  OBL_memmove SEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros CSUM MSUM cs cs' E fx R M model T HC _ Hn Hk. unfold node_memmove in Hn.
  destruct (dst_owned cs) eqn:Hd; [|discriminate].
  pose proof (dst_owned_range SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model HC Hd) as HOWN.
  destruct (summary_copy SEGS A nx0 cs (g_memmove G)) as [cs1|] eqn:Hcp.
  - injection Hn as <-.
    eapply (summary_copy_gsound SEGS A nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps SEGS_wr
             (g_memmove G) cs cs1 E fx R M model T CSUM HC HOWN Hcp Hk).
  - exact (summary_move_gsound (g_memmove G) cs cs' E fx R M model T MSUM HC HOWN Hn Hk).
Qed.

End Sound.
End GNM.
End GlzNodesMove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module GlzNodesSound.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma RUN_sound_fx : forall SEGS, GPS.RUN_SOUND SEGS fx_ok.
Proof.
  intros SEGS t K fuel stops pc sr kn nx E M R fx Ht HR HK Hsr Hkn Hfx.
  exact (runTXF_sound SEGS t K fuel stops pc sr kn nx E M (seg_rom SEGS) R fx Ht HR HK Hsr Hkn Hfx).
Qed.

Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable IT : itab.
Hypothesis IT_ok : itab_sound SEGS IT.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.
(* [comment removed for export] *)
Hypothesis ROM_ok : forall x : word, g_ro_lo G <= bv_unsigned x -> bv_unsigned x < g_ro_hi G -> seg_rom SEGS x <> None.
Hypothesis RO_hi : g_ro_hi G < 2 ^ 64.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).

Lemma rdn_rom_some : forall mem n (a : word),
  g_ro_lo G <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= g_ro_hi G ->
  exists bs, rdn SEGS mem a n = Some bs.
Proof.
  intros mem n. induction n as [|n IH]; intros a Hlo Hhi.
  - exists []. reflexivity.
  - cbn [rdn].
    assert (Hb : exists b, match mem a with Some b => Some b | None => seg_rom SEGS a end = Some b).
    { destruct (mem a) as [b|]; [exists b; reflexivity|].
      destruct (seg_rom SEGS a) as [b|] eqn:Hr; [exists b; reflexivity|].
      exfalso. apply (ROM_ok a); [lia | lia | exact Hr]. }
    destruct Hb as [b ->].
    pose proof (u64_range a) as Ha.
    destruct (IH (a + 1)%bv) as [bs ->].
    + rewrite u_add1 by lia. lia.
    + rewrite u_add1 by lia. lia.
    + exists (b :: bs). reflexivity.
Qed.

Lemma v_addi_pc4 : forall p, 0 <= p -> p + 4 < two64 -> v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
  intros p H0 H4. unfold v_addi. f_equal. rewrite Z_to_bv_unsigned. unfold two64 in H4.
  rewrite bv_wrap_small; [reflexivity | unfold bv_modulus; lia].
Qed.

Lemma load_range_fact_ok : forall E M sz sx v bs,
  length bs = GxSymStepR.msize_bytes sz ->
  ev E v = load_result sz sx bs ->
  know_ok SEGS E M (load_range_fact sz sx v).
Proof.
  intros E M sz sx v bs Hlen Hv. unfold know_ok, load_range_fact.
  pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hb0. rewrite Hlen in Hb.
  rewrite (load_result_val sz sx bs Hlen) in Hv.
  destruct sz, sx; cbn [GxSymStepR.msize_bytes msize_bytes] in *;
    first [ apply Forall_nil
          | constructor; [| apply Forall_nil]; cbn [kentry_ok edenot]; rewrite Hv; unfold extz, eff_sx;
            cbn in Hb; rewrite u_small by lia; lia ].
Qed.

Theorem node_imgload_sound : OBL_imgload SEGS IT nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros cs cs' E fx R M model T HC _ Hn Hk.
  unfold node_imgload in Hn.
  destruct (itab_lookup IT (pc cs)) as [i|] eqn:Hit.
  2:{ injection Hn as <-. apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]. }
  destruct i as [| | | | |sz sx rd rs imm| | | | | | | | | | | | | | | | | | | | | | | | | | | | |];
    try (injection Hn as <-; apply (Hk E fx R M model); [split; apply env_agree_refl | exact HC | reflexivity]).
  set (ae := eaddz (sr_get (s_regs (a_ss cs)) rs) (bv_signed imm)) in Hn.
  destruct (xlo (kn cs) ae) as [lo|] eqn:Hxlo; [|discriminate].
  destruct (xhi (kn cs) ae) as [hi|] eqn:Hxhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hpc4]. apply andb_prop in Hc as [Hc Hpc0].
  apply andb_prop in Hc as [Hc Hrd]. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hfresh Hlo].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hpc0. apply Z.ltb_lt in Hpc4.
  apply negb_true_iff in Hrd. apply Nat.eqb_eq in Hlen.
  pose proof (IT_ok _ _ Hit) as Hen. unfold itab_entry in Hen.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hf; [|discriminate].
  destruct (is_ecall w) eqn:Hec; [discriminate|].
  destruct (decode_any w) as [[i' isz]|] eqn:Hd; [|discriminate].
  destruct (Z.eqb isz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst isz.
  injection Hen as ->.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_regs HC) as HR.
  pose proof (co_know HC) as HK.
  assert (Haddr : v_addi (getr R rs) (bv_signed imm) = edenot E ae).
  { unfold ae, eaddz. rewrite mkAlu_denot. rewrite (HR rs). cbn [edenot]. rewrite alu_add. unfold v_addi, v_add.
    apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
  pose proof (xlo_sound SEGS E M (kn cs) ae lo HK Hxlo) as Blo.
  pose proof (xhi_sound SEGS E M (kn cs) ae hi HK Hxhi) as Bhi.
  destruct (rdn_rom_some M (GxSymStepR.msize_bytes sz) (edenot E ae)) as [bs Hrdn]; [lia | |].
  { replace (Z.of_nat (GxSymStepR.msize_bytes sz)) with (Z.of_nat (msize_bytes sz)) by (destruct sz; reflexivity). lia. }
  pose proof (rdn_length _ _ _ _ _ Hrdn) as Hbslen.
  set (val := load_result sz sx bs).
  set (v := nxt cs) in *.
  set (E' := ext1 E v val).
  assert (Hag : env_agree v E E') by apply ext1_agree.
  set (R' := regupd R rd val).
  assert (Hstep : RiscvSemantics.step SEGS (mkstF fx R (Z_to_bv 64 (pc cs)) M (seg_rom SEGS))
                  = MachineOk (mkstF fx R' (Z_to_bv 64 (pc cs + 4)) M (seg_rom SEGS))).
  { unfold mkstF. rewrite <- !mkstR_None.
    rewrite (stepR_load fx SEGS R _ M (seg_rom SEGS) None w sz sx rd rs imm bs Hf Hec Hd).
    - rewrite Hrd. rewrite v_addi_pc4 by assumption. reflexivity.
    - rewrite Haddr. exact Hrdn. }
  unfold cfgF.
  eapply RZ_step; [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | exact Hstep |].
  pose proof (cs_ok_agree SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC'.
  specialize (Hk E' fx R' M model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc. apply Hk; [|reflexivity].
  eapply (cs_ok_frame SEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC' | | reflexivity | | exact (co_fx HC) |].
  - (* [comment removed for export] *) cbn [mk_ss s_regs].
    pose proof (regs_ok_agree' (nxt cs) E E' _ R Hag Fsr HR) as HR1.
    pose proof (regs_ok_upd E' (s_regs (a_ss cs)) R rd val (EVar v) HR1) as HR2.
    rewrite Hrd in HR2. apply HR2. cbn [edenot]. unfold E'. apply ext1_at.
  - (* [comment removed for export] *) cbn [mk_ss s_know]. unfold know_ok. apply Forall_app. split.
    + eapply load_range_fact_ok; [exact Hbslen|]. unfold E'. rewrite ext1_at. reflexivity.
    + eapply know_ok_agree'; [exact Hag | exact Fkn | exact HK].
  - (* [comment removed for export] *) intros a Ha. exfalso. apply Ha. reflexivity.
Qed.

End Sound.
End GlzNodesSound.
Module GlzNodesStr.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts GlzKnowLib GlzCallLib GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL. Import GNL.
Open Scope Z_scope.

Module GNS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section Sound.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP SEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS SEGS RZ.
Variable G : gtable.

#[local] Notation cs_ok := (GPS.cs_ok SEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation node1_stmt := (GPS.node1_stmt SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ).
#[local] Notation cfg := (cfgF SEGS).
#[local] Notation gcall1 := (gcall_node_sound SEGS nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree RZ RZ_msteps).

Lemma img_cov_sound : forall E M k a b,
  know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
  apply HK1. lia.
Qed.

Theorem node_strlen_sound :
  strlen_lit_spec SEGS (g_strlen G) (g_hello G) 11 (g_ro_lo G) (g_ro_hi G) ->
  OBL_strlen SEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  intros SUM cs cs' E fx R M model T HC _ Hn Hk.
  pose proof (co_know HC) as HKN. pose proof (co_regs HC) as HREGS.
  unfold node_strlen in Hn.
  destruct (Z.eqb (pc cs) (g_strlen G)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (reg_lit cs 10) as [a|] eqn:H10; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Ha Hcov]. apply Z.eqb_eq in Ha. subst a.
  destruct (ret_lit_sound E cs R ret HREGS Hret) as (R1 & Hrok & Hretr & _).
  destruct (reg_lit_sound E cs R 10 (g_hello G) HREGS ltac:(lia) H10) as [R10 Hh].
  pose proof (img_cov_sound E M (kn cs) _ _ HKN Hcov) as Himg.
  destruct (SUM fx M R (Z_to_bv 64 ret)
              ltac:(intros x Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply Himg; exact Hx) Hrok R1 R10)
    as (regs' & Hms & Hkept & Ha0).
  eapply (gcall1 cs cs' E fx fx R M model T ret (Some (ELit 11)) (kn cs) regs' M HC Hn).
  - rewrite Hpc. exact Hms.
  - exact (co_fx HC).
  - intros x Hx. exfalso. apply Hx. reflexivity.
  - exact Hkept.
  - cbn [edenot]. etransitivity; [exact Ha0 | apply bv_eq; reflexivity].
  - exact HKN.
  - exact Hk.
Qed.
End Sound.
End GNS.
End GlzNodesStr.
Module UbDrvNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Module DN.
(* [comment removed for export] *)
Definition P_STDIO_WRITE : Z := 0x69010.

Definition P_EXIT : Z := 0x65e50.
   (* [comment removed for export] *)
Definition P_EXIT_ECALL : Z := 0x65bc0.
Definition FILE1 : Z := 0x79ec8.          (* [comment removed for export] *)
Definition FILE2 : Z := 0x79dd8.          (* [comment removed for export] *)
Definition SBUF : Z := 0xab268.           (* [comment removed for export] *)
Definition SBUF_SZ : Z := 1024.
Definition TPV : Z := 0x8ab90.            (* [comment removed for export] *)
Definition TID_CELL : Z := 0x8aae8.       (* [comment removed for export] *)
Definition CANARY : Z := 0xaae00.         (* [comment removed for export] *)
Definition GOT_CANARY : Z := 0x78d60.
Definition FR_SW : Z := 112.              (* [comment removed for export] *)
Definition FR_EXIT : Z := 128.            (* [comment removed for export] *)
Definition UP_EXIT : Z := 16.             (* [comment removed for export] *)
Definition SPLO : Z := 2 ^ 32 + 144.      (* [comment removed for export] *)
Definition SPHI : Z := 2 ^ 47.
Definition RW_MAX : Z := 2 ^ 17.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_cells : list (Z * nat * Z) :=
  [(0xaae23, 1%nat, 0); (0xab250, 8%nat, 0); (0xab240, 8%nat, 0);                  (* [comment removed for export] *)
   (0x79fb0, 8%nat, FILE1); (0x79ec0, 8%nat, FILE2);                              (* [comment removed for export] *)
   (FILE2 + 140, 4%nat, 2 ^ 32 - 1)].                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Section Nodes.
Variable segs : list Segment.
Variable nx0 : nat.

Definition reg_is (cs : acs) (r : nat) (v : Z) : bool :=
  match reg_lit cs r with Some x => Z.eqb x v | None => false end.
Definition at_sys (cs : acs) (a7 : Z) : bool := (is_ecall_at segs cs && reg_is cs 17 a7)%bool.


(* [comment removed for export] *)
Definition cells_ok (k : list kentry) (cells : list (Z * nat * Z)) : bool :=
  forallb (fun c => match c with (a, w, v) =>
             match kreadZ segs k (ELit 0) a w with Some x => Z.eqb x (v mod two64) | None => false end end) cells.

(* [comment removed for export] *)
Definition kbytes (n : nat) (k : list kentry) (b : expr) (o : Z) : option (list Z) := kread_bytes segs n k b o.

(* [comment removed for export] *)
Definition range_pieces (k : list kentry) (p n : expr) : option (list spiece) :=
  let '(b, o) := split_lit p in
  match lit_of n with
  | Some 0 => Some []
  | Some m => if Z.ltb 4096 m then None else
              match kbytes (Z.to_nat m) k b o with Some bs => Some [SPLit bs] | None => None end
  | None => match List.find (fun K => match K with KBlob (SA kb ko) kl _ => expr_eqb kb b && Z.eqb ko o && expr_eqb kl n | _ => false end) k with
            | Some (KBlob _ _ j) => Some [SPBlob j]
            | _ => None
            end
  end.

(* [comment removed for export] *)
Definition sp_ok (cs : acs) (fr : Z) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  match xlo k sp, xhi k sp with
  | Some lo, Some hi => (Z.leb (SPLO + fr) lo && Z.leb hi SPHI && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - fr) (ELit fr))%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition sp_ok_up (cs : acs) (fr up : Z) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  match xlo k sp, xhi k sp with
  | Some lo, Some hi => (Z.leb (SPLO + fr) lo && Z.leb (hi + up) SPHI && Z.leb 4 (ealign k sp) && kwritable_x k k spb (spk - fr) (ELit (fr + up)))%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition frame_ok (cs : acs) (fr : Z) : bool :=
  let '(spb, spk) := split_lit (reg cs 2) in in_floor (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - fr) (ELit fr).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ssp_ok (k : list kentry) : bool :=
  match kreadZ segs k (ELit 0) GOT_CANARY 8, kread8e segs k (ELit 0) CANARY with
  | Some g, Some _ => Z.eqb g CANARY
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition node_ioctl (cs : acs) : option acs :=
  if (at_sys cs 29 && (reg_is cs 10 1 || reg_is cs 10 2) && reg_is cs 11 0x5413)%bool
  then Some (set_pc (set_reg cs 10 (ELit (two64 - 25))) (pc cs + 4)) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition file_lits (k : list kentry) (f : Z) : option (Z * Z * Z * Z * Z) :=
  match kreadZ segs k (ELit 0) (f + 120) 4, kreadZ segs k (ELit 0) (f + 88) 8, kreadZ segs k (ELit 0) (f + 96) 8,
        kreadZ segs k (ELit 0) (f + 56) 8, kreadZ segs k (ELit 0) (f + 40) 8 with
  | Some fd, Some buf, Some bsz, Some wb, Some wp => Some (fd, buf, bsz, wb, wp)
  | _, _, _, _, _ => None
  end.

Definition node_stdio_write (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_STDIO_WRITE) then None else
  let k := kn cs in
  match reg_lit cs 10, ret_lit cs with
  | Some f, Some ret =>
      if negb ((Z.eqb f FILE1 || Z.eqb f FILE2) && sp_ok cs FR_SW && frame_ok cs FR_SW && ssp_ok k && fresh_ok nx0 cs
               && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then None else
      match file_lits k f with
      | Some (fd, buf, bsz, wb, wp) =>
          if negb (((Z.eqb fd 1 && Z.eqb f FILE1) || (Z.eqb fd 2 && Z.eqb f FILE2))                   (* [comment removed for export] *)
                   && Z.leb wb wp && Z.leb (wp - wb) 2048
                   && ((Z.eqb wb 0 && Z.eqb wp 0) || (Z.leb 0x79000 wb && Z.leb wp 0xac000))       (* [comment removed for export] *)
                   && Z.leb 0x79000 buf && Z.leb (buf + bsz) 0xac000 && Z.leb 0 bsz)%bool then None else
          let s := reg cs 11 in let l := reg cs 12 in
          let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
          (* [comment removed for export] *)
          let lok := match xhi k l, xhi k s with
                     | Some lh, Some sh => (Z.leb (wp - wb + lh) RW_MAX && Z.leb (sh + lh) SPHI)%bool
                     | _, _ => false end in
          let sdisj := (bflat_x k sb sk l && disj_x k sb sk l spb (spk - FR_SW) (ELit FR_SW))%bool in
          if negb (lok && sdisj)%bool then None else
          match kbytes (Z.to_nat (wp - wb)) k (ELit 0) wb, range_pieces k s l with
          | Some pend, Some ext =>
              let k1 := kn_havoc k spb (spk - FR_SW) (ELit FR_SW) in
              let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 32) in
              let k3 := [KWord (SA (ELit 0) (f + 32)) 8 (ELit (buf + bsz)); KWord (SA (ELit 0) (f + 40)) 8 (ELit buf);
                         KWord (SA (ELit 0) (f + 56)) 8 (ELit buf)] ++ k2 in
              match after_call nx0 cs ret (Some l) k3 with
              | Some cs' => Some (fd, (match pend with [] => [] | _ => [SPLit pend] end) ++ ext, cs')
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_covers (k : list kentry) (a n : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => (Z.leb lo a && Z.leb (a + n) hi)%bool | _ => false end) k.

Definition stdout_pending (k : list kentry) : option (list Z) :=
  if kimg_covers k FILE1 232 then Some [] else
  match kreadZ segs k (ELit 0) (FILE1 + 140) 4, kreadZ segs k (ELit 0) (FILE1 + 72) 8, kreadZ segs k (ELit 0) (FILE1 + 120) 4,
        kreadZ segs k (ELit 0) (FILE1 + 88) 8, kreadZ segs k (ELit 0) (FILE1 + 96) 8 with
  | Some lock, Some wr, Some fd, Some buf, Some bsz =>
      if negb (Z.eqb lock (2 ^ 32 - 1) && Z.eqb wr P_STDIO_WRITE && Z.eqb fd 1 && Z.eqb buf SBUF && Z.eqb bsz SBUF_SZ)%bool then None else
      match kreadZ segs k (ELit 0) (FILE1 + 56) 8, kreadZ segs k (ELit 0) (FILE1 + 40) 8,
            kreadZ segs k (ELit 0) (FILE1 + 8) 8, kreadZ segs k (ELit 0) (FILE1 + 16) 8 with
      | Some wb, Some wp, Some rp, Some re =>
          if negb (Z.eqb rp re && Z.leb 0xaae08 wb && Z.leb wb wp && Z.leb wp 0xac000 && Z.leb (wp - wb) RW_MAX)%bool then None else
          if Z.eqb wb wp then Some [] else if ssp_ok k then kbytes (Z.to_nat (wp - wb)) k (ELit 0) wb else None
      | _, _, _, _ => None
      end
  | _, _, _, _, _ => None
  end.

Definition exit_succ (cs : acs) : acs := set_pc (set_reg (set_reg cs 10 (reg cs 8)) 17 (ELit 94)) P_EXIT_ECALL.   (* [comment removed for export] *)

Definition node_exit (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_EXIT) then None else
  let k := kn cs in
  match reg_lit cs 8, reg_lit cs 4 with                                  (* [comment removed for export] *)
  | Some _, Some tp =>
      if negb (Z.eqb tp TPV && sp_ok_up cs FR_EXIT UP_EXIT && cells_ok k exit_cells && Nat.eqb (length (s_regs (a_ss cs))) 32
              )%bool then None else
      (* [comment removed for export] *)
      match kread8e segs k (ELit 0) (FILE2 + 40), kread8e segs k (ELit 0) (FILE2 + 56),
            kread8e segs k (ELit 0) (FILE2 + 8), kread8e segs k (ELit 0) (FILE2 + 16) with
      | Some w2, Some b2, Some r2, Some e2 =>
          if negb (expr_eqb w2 b2 && expr_eqb r2 e2)%bool then None else
          match stdout_pending k with
          | Some bs => Some (1, (match bs with [] => [] | _ => [SPLit bs] end), exit_succ cs)
          | None => None
          end
      | _, _, _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition XNd (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with 63%nat => node_ioctl cs | _ => None end.
Definition XEd (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 64%nat => node_stdio_write cs
  | 65%nat => node_exit cs
  | _ => None
  end.
End Nodes.
End DN.
End UbDrvNodes.
Module UbDrvNodes2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzNodesBlob UbDrvNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Module DN2.
Import DN.
Section Nodes.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
Definition file_syms (k : list kentry) (f : Z) : option (Z * expr * expr * expr * expr) :=
  match kreadZ segs k (ELit 0) (f + 120) 4, kread8e segs k (ELit 0) (f + 88), kread8e segs k (ELit 0) (f + 96),
        kread8e segs k (ELit 0) (f + 56), kread8e segs k (ELit 0) (f + 40) with
  | Some fd, Some buf, Some bsz, Some wb, Some wp => Some (fd, buf, bsz, wb, wp)
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)

Definition node_stdio_write2 (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) P_STDIO_WRITE) then None else
  let k := kn cs in
  match reg_lit cs 10, ret_lit cs with
  | Some f, Some ret =>
      if negb ((Z.eqb f FILE1 || Z.eqb f FILE2) && sp_ok cs FR_SW && frame_ok cs FR_SW && ssp_ok segs k && fresh_ok nx0 cs
               && Nat.eqb (length (s_regs (a_ss cs))) 32)%bool then None else
      match file_syms k f with
      | Some (fd, buf, bsz, wb, wp) =>
          if negb ((Z.eqb fd 1 && Z.eqb f FILE1) || (Z.eqb fd 2 && Z.eqb f FILE2))%bool then None else
          let s := reg cs 11 in let l := reg cs 12 in
          let '(wbb, wbk) := split_lit wb in let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
          match GNB.kgather segs k wb wp, GNB.kgather segs k s (eadd s l) with
          | Some pend, Some ext =>
              (* [comment removed for export] *)
              let ok := (lin_ge0 k [(ELit 0, SPHI)] [(wp, 0)] && lin_ge0 k [(ELit 0, SPHI)] [(s, 0); (l, 0)]
                         && lin_ge0 k [(wb, 2 ^ 30)] [(wp, 0); (l, 0)]
                         && bflat_x k wbb wbk (esub wp wb) && disj_x k wbb wbk (esub wp wb) spb (spk - FR_SW) (ELit FR_SW)
                         && bflat_x k sb sk l && disj_x k sb sk l spb (spk - FR_SW) (ELit FR_SW))%bool in
              if negb ok then None else
              let k1 := kn_havoc k spb (spk - FR_SW) (ELit FR_SW) in
              let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 32) in
              let k3 := [KWord (SA (ELit 0) (f + 32)) 8 (eadd buf bsz); KWord (SA (ELit 0) (f + 40)) 8 buf;
                         KWord (SA (ELit 0) (f + 56)) 8 buf] ++ k2 in
              match after_call nx0 cs ret (Some l) k3 with
              | Some cs' => Some (fd, pend ++ ext, cs')
              | None => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition P_STRNLEN : Z := 0x739f0.
Definition FR_SNL : Z := 32.
Definition node_strnlen (nzb : list nat) (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) P_STRNLEN) then None else
  let k := kn cs in
  match reg_lit cs 11, ret_lit cs with
  | Some n, Some ret =>
      if negb (sp_ok cs FR_SNL && frame_ok cs FR_SNL && fresh_ok nx0 cs && Nat.eqb (length (s_regs (a_ss cs))) 32
               && kimg_covers k 0x13038 32 && Z.leb 0 n && Z.ltb n two64)%bool then None else
      let s := reg cs 10 in let '(sb, sk) := split_lit s in let '(spb, spk) := split_lit (reg cs 2) in
      match find (fun K => match K with KBlob (SA b o) _ j => expr_eqb b sb && Z.eqb o sk && existsb (Nat.eqb j) nzb | _ => false end) k with
      | Some (KBlob _ L _) =>
          let ok := (existsb (kentry_eqb (KWord (SA (eadd s L) 0) 1 (ELit 0))) k
                     && existsb (fun K => match K with KUnk (SA b o) m => expr_eqb b sb && Z.eqb o sk && lin_ge0 k [(m, 0)] [(L, 8)] | _ => false end) k
                     && match xhi k L with Some lh => Z.leb (lh + 8) n | None => false end
                     && bflat_x k sb sk (eadd L (ELit 8))
                     && disj_x k sb sk (eadd L (ELit 8)) spb (spk - FR_SNL) (ELit FR_SNL)
                     && lin_ge0 k [(ELit 0, SPHI)] [(s, 0); (L, 8)]
                     && lin_ge0 k [(s, 0)] [(ELit 1, 0)])%bool in
          if negb ok then None else
          after_call nx0 cs ret (Some L) (kn_havoc k spb (spk - FR_SNL) (ELit FR_SNL))
      | _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_read_dir (cs : acs) : option acs :=
  match reg_lit cs 11, reg_lit cs 12 with
  | Some b, Some c =>
      if (at_sys segs cs 63 && reg_is cs 10 3 && Z.leb 0 b && Z.leb 0 c && Z.leb (b + c) (2 ^ 47))%bool
      then Some (set_pc (set_reg cs 10 (ELit (two64 - 21))) (pc cs + 4)) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition XNe (G : gtable) (nzb : list nat) (dird : bool) (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 63%nat => node_ioctl segs cs
  | 1%nat => node_memcpy segs A nx0 G cs
  | 5%nat => GNB.node_memcpy_blob A nx0 G cs
  | 67%nat => node_strnlen nzb cs
  | 68%nat => if dird then node_read_dir cs else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition XEe (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 66%nat => node_stdio_write2 cs
  | _ => XEd segs nx0 id args cs
  end.
End Nodes.
End DN2.
End UbDrvNodes2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.

#[local] Notation W8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Lemma lor7_bounds : forall x, (0 <= x)%Z -> (x <= Z.lor x 7 <= x + 7)%Z.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as E.
  pose proof (Z.land_nonneg x 7) as N. pose proof (AX2S.land_le_r x 7 Hx ltac:(lia)) as U. lia.
Qed.

(* [comment removed for export] *)
Definition galloc (n cap : Z) : Z := Z.lor (Z.max n (2 * cap)) 7 + 1.

(* [comment removed for export] *)
Definition kept15 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Keep.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition resize_keepS_spec (entry : Z) : Prop :=
  forall fx regs M (obj sp ret w0 cw : word) (s n : Z),
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 mod 256 = 2 * s -> 0 <= s <= 22 -> 0 <= n <= 22 ->
    bv_unsigned obj + 24 <= 2 ^ 64 -> 80 <= bv_unsigned sp ->
    (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj) ->
    store_ok SEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true -> store_ok SEGS M obj 24 = true ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 10%bv = obj -> getr regs 11%bv = Z_to_bv 64 n ->
    getr regs 12%bv = cw ->
    exists r' M',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) M (seg_rom SEGS)) (mkstF fx r' ret M' (seg_rom SEGS))
      /\ getr r' 10%bv = obj
      /\ (forall x : bv 5, In x kept15 -> getr r' x = getr regs x)
      /\ (forall a : word, M' a <> M a ->
            bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)
      /\ mem_grows M M'
      /\ rdn SEGS M' obj 1 = Some [Z_to_bv 8 (2 * n)]
      /\ M' (Z_to_bv 64 (bv_unsigned obj + 1 + n)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition resize_keepL_spec (entry : Z) : Prop :=
  forall fx regs M (obj sp ret d w0 cw : word) (cap s n : Z),
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 = cap + 2 -> (cap + 1) mod 2 = 0 ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
    0 <= s <= cap -> 0 <= n <= cap -> cap < 2 ^ 62 ->
    bv_unsigned obj + 24 <= 2 ^ 64 -> bv_unsigned d + cap + 1 <= 2 ^ 64 -> 80 <= bv_unsigned sp ->
    (bv_unsigned obj + 24 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned obj) ->
    (bv_unsigned d + cap + 1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned d) ->
    (bv_unsigned d + cap + 1 <= bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned d) ->
    store_ok SEGS M (Z_to_bv 64 (bv_unsigned sp - 80)) 80 = true -> store_ok SEGS M obj 24 = true ->
    store_ok SEGS M d (Z.to_nat (cap + 1)) = true ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 10%bv = obj -> getr regs 11%bv = Z_to_bv 64 n ->
    getr regs 12%bv = cw ->
    exists r' M',
      msteps SEGS (mkstF fx regs (Z_to_bv 64 entry) M (seg_rom SEGS)) (mkstF fx r' ret M' (seg_rom SEGS))
      /\ getr r' 10%bv = obj
      /\ (forall x : bv 5, In x kept15 -> getr r' x = getr regs x)
      /\ (forall a : word, M' a <> M a ->
            bv_unsigned obj + 8 <= bv_unsigned a < bv_unsigned obj + 16
            \/ bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1
            \/ bv_unsigned sp - 80 <= bv_unsigned a < bv_unsigned sp)
      /\ mem_grows M M'
      /\ rdn SEGS M' obj 8 = Some (W8 w0)
      /\ rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n))
      /\ rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d)
      /\ M' (Z_to_bv 64 (bv_unsigned d + n)) = Some (Z_to_bv 8 0).
End Keep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Machine.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Variable G : gtable.

(* [comment removed for export] *)
Definition resize_growS_mspec (stk bc cc : Z) (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret sp : Z) (obj w0 cw : word) (s n : Z) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV Lc B C M mdl ->
    T [] ->     (* [comment removed for export] *)
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = obj -> getr R (Z_to_bv 5 11) = Z_to_bv 64 n -> getr R (Z_to_bv 5 12) = cw ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + stk + 80 <= sp ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - stk - 80 <= bv_unsigned a < sp -> store_ok SEGS M a 1 = true) ->
    sp <= bv_unsigned obj -> bv_unsigned obj + 24 <= 2 ^ 64 -> store_ok SEGS M obj 24 = true ->
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 mod 256 = 2 * s ->
    0 <= s <= 22 -> 22 < n -> 4 * n <= NMAX ->
    B + mcost (galloc n 22) <= bc -> C + MCNT <= cc ->
    (forall fx' R' M' mdl' (p : word),
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        getr R' (Z_to_bv 5 10) = obj ->
        bv_unsigned p mod 16 = 0 -> blk_ok G (bv_unsigned p) (galloc n 22) ->
        (forall b m, In (b, m) Lc -> bv_unsigned p + galloc n 22 <= b \/ b + m <= bv_unsigned p) ->
        (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + galloc n 22 -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        rdn SEGS M' obj 8 = Some (W8 (Z_to_bv 64 (galloc n 22 + 1))) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 p) ->
        M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
        (forall a : word, M' a <> M a ->
           bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 \/ alloc_changed G (stk + 80) Lc sp a) ->
        (forall a : word, sp - stk - 80 <= bv_unsigned a < sp -> store_ok SEGS M' a 1 = true) ->
        (forall a : word, bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 -> M' a <> None) ->
        AINV ((bv_unsigned p, galloc n 22) :: Lc) (B + mcost (galloc n 22)) (C + MCNT) M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.

(* [comment removed for export] *)
Definition resize_growL_mspec (stk bc cc : Z) (entry : Z) : Prop :=
  forall fx R M mdl L1 L2 B C (ret sp : Z) (obj d w0 cw : word) (cap s n : Z) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV (L1 ++ (bv_unsigned d, cap + 1) :: L2) B C M mdl ->
    T [] ->     (* [comment removed for export] *)
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = obj -> getr R (Z_to_bv 5 11) = Z_to_bv 64 n -> getr R (Z_to_bv 5 12) = cw ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + stk + 80 <= sp ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - stk - 80 <= bv_unsigned a < sp -> store_ok SEGS M a 1 = true) ->
    sp <= bv_unsigned obj -> bv_unsigned obj + 24 <= 2 ^ 64 -> store_ok SEGS M obj 24 = true ->
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 = cap + 2 -> (cap + 1) mod 8 = 0 -> 23 <= cap ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
    0 <= s <= cap -> cap < n -> 4 * n <= NMAX -> 4 * cap <= NMAX ->
    blk_ok G (bv_unsigned d) (cap + 1) ->
    (forall a : word, bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> M a <> None /\ store_ok SEGS M a 1 = true) ->
    B + mcost (galloc n cap) <= bc -> C + MCNT <= cc ->
    (forall fx' R' M' mdl' (p : word),
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        getr R' (Z_to_bv 5 10) = obj ->
        bv_unsigned p mod 16 = 0 -> blk_ok G (bv_unsigned p) (galloc n cap) ->
        (forall b m, In (b, m) (L1 ++ L2) -> bv_unsigned p + galloc n cap <= b \/ b + m <= bv_unsigned p) ->
        (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + galloc n cap -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        rdn SEGS M' obj 8 = Some (W8 (Z_to_bv 64 (galloc n cap + 1))) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 p) ->
        M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
        (forall a : word, M' a <> M a ->
           bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 \/ alloc_changed G (stk + 80) (L1 ++ L2) sp a) ->
        (forall a : word, sp - stk - 80 <= bv_unsigned a < sp -> store_ok SEGS M' a 1 = true) ->
        (forall a : word, bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 -> M' a <> None) ->
        AINV ((bv_unsigned p, galloc n cap) :: L1 ++ L2)
             (Z.max 0 (B + mcost (galloc n cap) - mcost (cap + 1))) (Z.max 0 (C + MCNT - MCNT)) M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.
End Machine.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Node.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Variable G : gtable.
Variable bcap ccap : Z.

#[local] Notation frame_kept := (GlzContracts.frame_kept SWIN PERMc SPTOPc G).

(* [comment removed for export] *)
Definition obj_ok (Lo : list (Z * Z)) (M : word -> option byte) (sp : Z) (obj : word) : Prop :=
  sp <= bv_unsigned obj /\ bv_unsigned obj + 24 <= 2 ^ 64 /\ store_ok SEGS M obj 24 = true
  /\ (forall a : word, bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 -> owned SWIN PERMc SPTOPc Lo a).

Definition resize_growS_nspec (entry : Z) : Prop :=
  forall fx R M mdl Lc B C (ret sp : Z) (obj w0 cw : word) (s n : Z) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV Lc B C M mdl ->
    T [] ->     (* [comment removed for export] *)
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = obj -> getr R (Z_to_bv 5 11) = Z_to_bv 64 n -> getr R (Z_to_bv 5 12) = cw ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + MSTK <= sp -> sp <= SPTOPc ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - MSTK <= bv_unsigned a < sp -> store_ok SEGS M a 1 = true) ->
    obj_ok Lc M sp obj ->
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 mod 256 = 2 * s ->
    0 <= s <= 22 -> 22 < n -> 4 * n <= NMAX ->
    B + mcost (galloc n 22) <= bcap -> C + MCNT <= ccap ->
    (forall fx' R' M' mdl' (p : word),
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        getr R' (Z_to_bv 5 10) = obj ->
        bv_unsigned p mod 16 = 0 -> blk_ok G (bv_unsigned p) (galloc n 22) ->
        (forall b m, In (b, m) Lc -> bv_unsigned p + galloc n 22 <= b \/ b + m <= bv_unsigned p) ->
        (forall lo hi, In (lo, hi) PERMc -> lo < hi -> bv_unsigned p + galloc n 22 <= lo \/ hi <= bv_unsigned p) ->
        (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + galloc n 22 -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        rdn SEGS M' obj 8 = Some (W8 (Z_to_bv 64 (galloc n 22 + 1))) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 p) ->
        M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
        (forall a : word, frame_kept Lc sp a -> ~ (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24) -> M' a = M a) ->
        (forall a : word, sp - MSTK <= bv_unsigned a < sp -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        (forall a : word, bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        AINV ((bv_unsigned p, galloc n 22) :: Lc) (B + mcost (galloc n 22)) (C + MCNT) M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.

Definition resize_growL_nspec (entry : Z) : Prop :=
  forall fx R M mdl L1 L2 B C (ret sp : Z) (obj d w0 cw : word) (cap s n : Z) T,
    m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> FXOK fx ->
    AINV (L1 ++ (bv_unsigned d, cap + 1) :: L2) B C M mdl ->
    T [] ->     (* [comment removed for export] *)
    getr R (Z_to_bv 5 1) = Z_to_bv 64 ret -> 0 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
    getr R (Z_to_bv 5 10) = obj -> getr R (Z_to_bv 5 11) = Z_to_bv 64 n -> getr R (Z_to_bv 5 12) = cw ->
    bv_unsigned (getr R (Z_to_bv 5 2)) = sp -> sp mod 16 = 0 -> CEIL_run + MSTK <= sp -> sp <= SPTOPc ->
    getr R (Z_to_bv 5 4) = Z_to_bv 64 (g_tp G) ->
    (forall a : word, sp - MSTK <= bv_unsigned a < sp -> store_ok SEGS M a 1 = true) ->
    obj_ok (L1 ++ L2) M sp obj ->
    rdn SEGS M obj 8 = Some (W8 w0) -> bv_unsigned w0 = cap + 2 -> (cap + 1) mod 8 = 0 -> 23 <= cap ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
    rdn SEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
    0 <= s <= cap -> cap < n -> 4 * n <= NMAX -> 4 * cap <= NMAX ->
    (bv_unsigned d + cap + 1 <= bv_unsigned obj \/ bv_unsigned obj + 24 <= bv_unsigned d) ->
    (forall a : word, bv_unsigned d <= bv_unsigned a < bv_unsigned d + cap + 1 -> store_ok SEGS M a 1 = true) ->
    B + mcost (galloc n cap) <= bcap -> C + MCNT <= ccap ->
    (forall fx' R' M' mdl' (p : word),
        FXOK fx' ->
        (forall r, In r callee_saved_regs -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
        getr R' (Z_to_bv 5 10) = obj ->
        bv_unsigned p mod 16 = 0 -> blk_ok G (bv_unsigned p) (galloc n cap) ->
        (forall b m, In (b, m) (L1 ++ L2) -> bv_unsigned p + galloc n cap <= b \/ b + m <= bv_unsigned p) ->
        (forall lo hi, In (lo, hi) PERMc -> lo < hi -> bv_unsigned p + galloc n cap <= lo \/ hi <= bv_unsigned p) ->
        (forall a : word, bv_unsigned p <= bv_unsigned a < bv_unsigned p + galloc n cap -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        rdn SEGS M' obj 8 = Some (W8 (Z_to_bv 64 (galloc n cap + 1))) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 n)) ->
        rdn SEGS M' (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 p) ->
        M' (Z_to_bv 64 (bv_unsigned p + n)) = Some (Z_to_bv 8 0) ->
        (forall a : word, frame_kept (L1 ++ L2) sp a -> ~ (bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24) -> M' a = M a) ->
        (forall a : word, sp - MSTK <= bv_unsigned a < sp -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        (forall a : word, bv_unsigned obj <= bv_unsigned a < bv_unsigned obj + 24 -> M' a <> None /\ store_ok SEGS M' a 1 = true) ->
        AINV ((bv_unsigned p, galloc n cap) :: L1 ++ L2)
             (Z.max 0 (B + mcost (galloc n cap) - mcost (cap + 1))) (Z.max 0 (C + MCNT - MCNT)) M' mdl' ->
        m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] -> m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl ->
        RZ (mkCfg (mkstF fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) mdl') T) ->
    RZ (mkCfg (mkstF fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) mdl) T.

(* [comment removed for export] *)
Record resize_specs (entry : Z) : Prop := RS {
  rs_keepS : resize_keepS_spec SEGS entry;
  rs_keepL : resize_keepL_spec SEGS entry;
  rs_growS : resize_growS_nspec entry;
  rs_growL : resize_growL_nspec entry }.
End Node.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mono.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Variable FXOK : FX -> Prop.
(* [comment removed for export] *)
Variable RZ : GPS.rz_t.
Variable G : gtable.
Hypothesis priv_below : forall z, in_wins (g_priv G) z -> z < CEIL_run.   (* [comment removed for export] *)

#[local] Notation malloc_mspecR := (GlzContracts.malloc_mspecR SEGS AINV FXOK RZ G).
#[local] Notation free_mspecR := (GlzContracts.free_mspecR SEGS AINV FXOK RZ G).

Lemma alloc_changed_mono : forall stk stk' Lc sp a,
  stk <= stk' -> alloc_changed G stk Lc sp a -> alloc_changed G stk' Lc sp a.
Proof.
  intros stk stk' Lc sp a Hle [H|[H|H]]; [left; exact H | right; left; lia | right; right; exact H].
Qed.

Lemma scratch_unchanged : forall stk Lc sp (M M' : word -> option byte) (a : word),
  (forall a : word, M' a <> M a -> alloc_changed G stk Lc sp a) ->
  CEIL_run <= bv_unsigned a -> bv_unsigned a < sp - stk -> M' a = M a.
Proof.
  intros stk Lc sp M M' a Hch H1 H2. destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
  destruct (Hch a NE) as [[Hz _]|[Hs|Hp]]; [lia | lia | pose proof (priv_below _ Hp); lia].
Qed.

Lemma store_ok1_ext : forall (M M' : word -> option byte) (a : word),
  M' a = M a -> RiscvSemantics.store_ok SEGS M' a 1 = RiscvSemantics.store_ok SEGS M a 1.
Proof. intros M M' a E. cbn [RiscvSemantics.store_ok]. unfold wview. rewrite E. reflexivity. Qed.






Lemma free_mspecR_mono : forall stk stk' entry,
  0 <= stk <= stk' -> free_mspecR stk entry -> free_mspecR stk' entry.
Proof.
  intros stk stk' entry Hstk FRE fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hlz Hmat HFX HA R1 Rr Re R10 Hcase R2 Hal Hsp R4 Hscr K.
  apply (FRE fx R M mdl Lc Lc' B C B' C' ret sp p T Hh Hlz Hmat HFX HA R1 Rr Re R10 Hcase R2 Hal ltac:(lia) R4
           ltac:(intros a Ha; apply Hscr; lia)).
  intros fx' R' M' mdl' HFX' Hkept Hch Hscr' HA' Hh' Hlz' Hmat' Hfs' Hfds'.
  apply (K fx' R' M' mdl' HFX' Hkept); try assumption.
  - intros a Ha. eapply alloc_changed_mono; [|exact (Hch a Ha)]. lia.
  - intros a Ha. destruct (Z.lt_ge_cases (bv_unsigned a) (sp - stk)) as [Hlt|Hge].
    + rewrite (store_ok1_ext M M' a (scratch_unchanged stk Lc' sp M M' a Hch ltac:(lia) Hlt)). apply Hscr. exact Ha.
    + apply Hscr'. lia.
Qed.
End Mono.
