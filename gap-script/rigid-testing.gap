LoadPackage("qpa");
LoadPackage("yags");
LoadPackage("Float");
Q := Quiver(4, [[1,2,"alpha"],[1,2,"beta"],[2,1,"gamma"],[2,1,"delta"],[3,4,"a"],[3,4,"b"],[4,3,"e"],[4,3,"f"],[1,3,"brigde"]]);
#Q := Quiver(4, [[1,2,"a"],[1,2,"b"],[2,1,"o"],[2,1,"k"],[1,3,"e"],[3,4,"f"],[3,4,"i"],[4,3,"j"],[4,3,"kp"] ] );
#Q := Quiver(2, [[1,2,"a"],[1,2,"b"],[2,1,"c"],[2,1,"d"]]);
#Q := Quiver(4,[[1,3,"a"],[1,4,"b"],[3,4,"c"],[3,2,"d"],[4,2,"e"]]);


Display(Q);

KQ := PathAlgebra(GF(2),Q);

AssignGeneratorVariables(KQ);


stop := 1;

rels := [];
AddNthPowerToRelations(KQ,rels,2);

KQ := KQ/rels;

inj := IndecInjectiveModules(KQ);


#/[x1*x2,x2*x1,y1*y2,y2*y1,x1*y2-y2*x1,x2*y1-y1*x2];

#/[a*b];

LeftMutation := function(x,u)
    local g, y, test;
    g := LeftApproximationByAddM(x,u);
    Display("approximation ok");
    y := CoKernel(g);
    Display("Cokernel ok");
    
    
    test := MaximalCommonDirectSummand( u, y );
    
    # Needed, as the type of test is not known
    if (FamilyObj(test) = FamilyObj(1=1)) then
        return y;
    fi;

    while Dimension(test[1][1]) <> 0 do
          y:= test[ 3 ];
          test := MaximalCommonDirectSummand( u, test[ 3 ] );
          
          if (FamilyObj(test) = FamilyObj(1=1)) then
              return y;
          fi;
    od;
    
    return test[ 3 ];
end;



proj := IndecProjectiveModules(KQ);

LeftMutateOnList := function(m,i)
    local j,u,x,y;
    
    j := 1;
    u := [];
        
    while j <= Length(m) do
        if not j = i then
            Add(u,m[j]);
        fi;
        j := j + 1;
        
    od;
        
    x := m[i];
    y := LeftMutation(x,DirectSumOfQPAModules(u));
    
    return y;
end;

GetBoundedMutations := function(tau_tilt,depth,i,nogo)
    local j,y,mutation_j,all_mutations,testz,haszerosummand;

    if i > depth then
        return [];
    fi;
    
    all_mutations := [];
    
    j := 1;
    while j <= Length(tau_tilt) do
        
        if j = nogo then
            j := j + 1;
            continue;
        fi;
        
        y := LeftMutateOnList(tau_tilt,j);
        
        mutation_j := ShallowCopy(tau_tilt);
        mutation_j[j] := y;
        
        if not IsTauRigidModule(DirectSumOfQPAModules(mutation_j)) then
            j := j + 1;
            continue;
        fi;
        
        
        for k in all_mutations do
            if IsomorphicModules(DirectSumOfQPAModules(k),DirectSumOfQPAModules(mutation_j)) then
                j := j + 1;
                continue;
            fi;
        od;
        
        if IsomorphicModules(y,ZeroModule(KQ)) then
            j := j + 1;
            Add(all_mutations,mutation_j);
            continue;
        fi;
        
        
       
        
        testz := 1;
        haszerosummand := 0;
        
        
        Add(all_mutations,mutation_j);
        
        
        Append(all_mutations,GetBoundedMutations(mutation_j,depth,i+1,j));
        
        j := j + 1;
    od;
    
    return all_mutations;
end;

    
# Are two tau-tilting modules given as lists isomorphic?
EqualUpToOrder := function(m,n)
    local i;
    if not Length(m) = Length(n) then
        return False;
    fi;
    
    g := SymmetricGroup(Length(m));
    
    for p in g do
        lp := ListPerm(p,Length(m));
        
        m2 := [];
        for i in lp do
            Add(m2,m[i]);
        od;
        
        # iso?
        i := 1;
        alliso := true;
        while i <= Length(m2) do
            if not IsomorphicModules(m2[i],n[i]) then
                alliso := false;
            fi;
            
            i := i + 1;
        od;
        
        if alliso then
            return true;
        fi;
        
    od;
    
    return false;
end;


modulei := function(i)
    #f := LeftApproximationByAddM(proj[1],proj[2]);
    #Display(f);
    #alpha := DirectSumProjections(Range(f))[1];
    #beta := DirectSumProjections(Range(f))[2];
    
    hom := HomOverAlgebra(proj[1],proj[2]);
    alpha := hom[1];
    beta := hom[2];
    
    p2 := [proj[2]];
    p1 := [];
    j := 1;
    while(j <= i) do
        Add(p1,proj[1]);
        Add(p2,proj[2]);
        j := j + 1;
    od;
    
    pp2 := DirectSumOfQPAModules(p2);
    pp1 := DirectSumOfQPAModules(p1);
    
    proj1 := DirectSumProjections(pp1);
    inc2 := DirectSumInclusions(pp2);
    
    g := ZeroMapping(pp1,pp2);
    
    j := 1;
    while(j <= i) do
        #Display(Range(alpha));
        #Display(Source(inc2[j]));
        #Display(Range(alpha) = Source(inc2[j]));
        #Display(alpha*inc2[j]);
        
        g := g + proj1[j]*alpha*inc2[j];
        g := g + proj1[j]*beta*inc2[j+1];
        
        #g := g + proj1[j]*f*alpha*inc2[j];
        #g := g + proj1[j]*f*beta*inc2[j+1];
        
        j := j+1;
    od;
    
    return g;
    
end;

moduleOp := function(i)
    #f := LeftApproximationByAddM(proj[1],proj[2]);
    #Display(f);
    #alpha := DirectSumProjections(Range(f))[1];
    #beta := DirectSumProjections(Range(f))[2];
    
    hom := HomOverAlgebra(proj[2],proj[1]);
    alpha := hom[1];
    beta := hom[2];
    
    p2 := [proj[1]];
    p1 := [];
    j := 1;
    while(j <= i) do
        Add(p1,proj[2]);
        Add(p2,proj[1]);
        j := j + 1;
    od;
    
    pp2 := DirectSumOfQPAModules(p2);
    pp1 := DirectSumOfQPAModules(p1);
    
    proj1 := DirectSumProjections(pp1);
    inc2 := DirectSumInclusions(pp2);
    
    g := ZeroMapping(pp1,pp2);
    
    j := 1;
    while(j <= i) do
        #Display(Range(alpha));
        #Display(Source(inc2[j]));
        #Display(Range(alpha) = Source(inc2[j]));
        #Display(alpha*inc2[j]);
        
        g := g + proj1[j]*alpha*inc2[j];
        g := g + proj1[j]*beta*inc2[j+1];
        
        #g := g + proj1[j]*f*alpha*inc2[j];
        #g := g + proj1[j]*f*beta*inc2[j+1];
        
        j := j+1;
    od;
    
    return g;
    
end;

projApprox := function(i)
    f := LeftApproximationByAddM(proj[1],proj[2]);
    #Display(f);
    alpha := DirectSumProjections(Range(f))[1];
    beta := DirectSumProjections(Range(f))[2];
    
    #hom := HomOverAlgebra(proj[1],proj[2]);
    #alpha := hom[1];
    #beta := hom[2];
    
    p2 := [proj[2]];
    p1 := [];
    j := 1;
    while(j <= i) do
        Add(p1,proj[1]);
        Add(p2,proj[2]);
        j := j + 1;
    od;
    
    pp2 := DirectSumOfQPAModules(p2);
    pp1 := DirectSumOfQPAModules(p1);
    
    proj1 := DirectSumProjections(pp1);
    inc2 := DirectSumInclusions(pp2);
    
    g := ZeroMapping(pp1,pp2);
    
    j := 1;
    while(j <= i) do
        #Display(Range(alpha));
        #Display(Source(inc2[j]));
        #Display(Range(alpha) = Source(inc2[j]));
        #Display(alpha*inc2[j]);
        
        #g := g + proj1[j]*alpha*inc2[j];
        #g := g + proj1[j]*beta*inc2[j+1];
        
        g := g + proj1[j]*f*alpha*inc2[j];
        g := g + proj1[j]*f*beta*inc2[j+1];
        
        j := j+1;
    od;
    
    return g;
    
end;


gmatrix := function(mm)
    local ans;
    ans := [];
    for m in mm do
        Add(ans,gvector(m));
    od;
    
    return ans;
end;
    


gvector := function(m)
    local pr,p1,p2,d_p1,d_p2,g_1,g_2;
    
    pr := ProjectiveResolution(m);
    p1 := Source(pr^1);
    p2 := Range(pr^1);
    
    # GET TOP OF MODULE HERE.

    return DimensionVector(TopOfModule(p2)) - DimensionVector(TopOfModule(p1));
end;


