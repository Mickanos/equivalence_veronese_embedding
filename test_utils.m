Prod := function(a,b)
    return a * b;
end function;

//Magma's Lie bracket does not work for matrices.
MyLieBracket := function(a,b)
    return a*b - b*a;
end function;
//Test if f is a homomorphism of Lie algebras.
//Works whether the domains and codomains of f are Lie algebras or
//Associative algebras.
IsLieHom := function(f, L)
    brack_dom := IsAssociative(Domain(f)) select MyLieBracket else Prod;
    brack_co := IsAssociative(Codomain(f)) select MyLieBracket else Prod;
    res := [<a,b> : a, b in L | brack_dom(a,b) @ f ne brack_co(a @ f, b @ f)];
    return IsEmpty(res), res;
end function;